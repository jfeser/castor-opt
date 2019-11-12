open! Core
open! Castor
open Collections
module A = Abslayout

module Config = struct
  module type S = sig
    include Ops.Config.S

    include Filter_tactics.Config.S

    include Simple_tactics.Config.S

    include Approx_cost.Config.S
  end
end

module Make (C : Config.S) = struct
  module O = Ops.Make (C)
  open O
  module S = Simple_tactics.Make (C)
  open S
  module R = Resolve
  module ACost = Approx_cost.Make (C)

  type t =
    | Flat of A.t
    | Hash of { lkey : A.pred; lhs : t; rkey : A.pred; rhs : t }
    | Nest of { lhs : t; rhs : t; pred : A.pred }
  [@@deriving sexp_of]

  let rec emit_joins =
    let module J = Join_elim_tactics.Make (C) in
    let open J in
    function
    | Flat _ -> row_store
    | Hash { lhs; rhs; _ } ->
        seq_many
          [
            at_ (emit_joins lhs) (child 0);
            at_ (emit_joins rhs) (child 1);
            elim_join_hash;
          ]
    | Nest { lhs; rhs; _ } ->
        seq_many
          [
            at_ (emit_joins lhs) (child 0);
            at_ (emit_joins rhs) (child 1);
            elim_join_nest;
          ]

  let reshape j _ =
    let rec to_ralgebra = function
      | Flat r -> r
      | Nest { lhs; rhs; pred } ->
          A.join pred (to_ralgebra lhs) (to_ralgebra rhs)
      | Hash { lkey; rkey; lhs; rhs } ->
          A.join (Binop (Eq, lkey, rkey)) (to_ralgebra lhs) (to_ralgebra rhs)
    in
    Some (to_ralgebra j)

  let mk_transform j = seq (of_func (reshape j)) (emit_joins j)

  let to_parts rhs pred =
    let rhs_schema = A.schema_exn rhs |> Set.of_list (module Name) in
    Pred.names pred |> Set.filter ~f:(Set.mem rhs_schema)

  let cost join =
    [|
      ACost.cost
        (Option.value_exn (O.apply (mk_transform join) Path.root A.empty));
    |]

  let opt_nonrec opt parts s =
    Logs.debug (fun m ->
        m "Choosing join for space %s." (Join_space.to_string s));
    if Join_space.length s = 1 then
      let j = Flat (Join_space.choose s) in
      Pareto_set.singleton (cost j) j
    else
      Join_space.partition_fold s ~init:Pareto_set.empty
        ~f:(fun cs (s1, s2, es) ->
          let pred = Pred.conjoin (List.map es ~f:(fun (_, p, _) -> p)) in
          (* Add flat joins to pareto set. *)
          let flat_joins =
            let select_flat s =
              List.filter_map (opt parts s) ~f:(fun (_, j) ->
                  match j with Flat r -> Some r | _ -> None)
            in
            List.cartesian_product (select_flat s1) (select_flat s2)
            |> List.map ~f:(fun (r1, r2) ->
                   let j = Flat (A.join pred r1 r2) in
                   (cost j, j))
            |> Pareto_set.of_list
          in
          (* Add nest joins to pareto set. *)
          let nest_joins =
            let lhs_parts =
              Set.union (to_parts (Join_space.to_ralgebra s1) pred) parts
            in
            let rhs_parts =
              Set.union (to_parts (Join_space.to_ralgebra s2) pred) parts
            in
            let lhs_set = List.map (opt lhs_parts s1) ~f:(fun (_, j) -> j) in
            let rhs_set = List.map (opt rhs_parts s2) ~f:(fun (_, j) -> j) in
            List.cartesian_product lhs_set rhs_set
            |> List.map ~f:(fun (j1, j2) ->
                   let j = Nest { lhs = j1; rhs = j2; pred } in
                   (cost j, j))
            |> Pareto_set.of_list
          in
          (* Add hash joins to pareto set. *)
          let hash_joins =
            let lhs_schema =
              A.schema_exn (Join_space.to_ralgebra s1)
              |> Set.of_list (module Name)
            in
            let rhs_schema =
              A.schema_exn (Join_space.to_ralgebra s2)
              |> Set.of_list (module Name)
            in
            (* Figure out which partition a key comes from. *)
            let key_side k =
              let rs = Pred.names k |> Set.to_list in
              if List.for_all rs ~f:(Set.mem lhs_schema) then Some s1
              else if List.for_all rs ~f:(Set.mem rhs_schema) then Some s2
              else None
            in
            let m_s =
              match pred with
              | A.Binop (Eq, k1, k2) ->
                  let open Option.Let_syntax in
                  let%bind s1 = key_side k1 in
                  let%map s2 = key_side k2 in
                  if Join_space.O.(s1 = s2) then []
                  else
                    let rhs_parts =
                      Set.union
                        (to_parts (Join_space.to_ralgebra s2) pred)
                        parts
                    in
                    List.cartesian_product (opt parts s1) (opt rhs_parts s2)
                    |> List.map ~f:(fun ((_, r1), (_, r2)) ->
                           Hash { lkey = k1; rkey = k2; lhs = r1; rhs = r2 })
              | _ -> None
            in
            Option.value m_s ~default:[] |> List.map ~f:(fun j -> (cost j, j))
          in
          Pareto_set.union_all [ cs; flat_joins; nest_joins; hash_joins ])

  let opt =
    let module Key = struct
      type t = Set.M(Name).t * Set.M(Join_graph.Vertex).t
      [@@deriving compare, hash, sexp_of]

      let create p s =
        ( p,
          Join_graph.fold_vertex
            (fun v vs -> Set.add vs v)
            s.Join_space.graph
            (Set.empty (module Join_graph.Vertex)) )
    end in
    let tbl = Hashtbl.create (module Key) in
    let rec opt p s =
      let key = Key.create p s in
      match Hashtbl.find tbl key with
      | Some v -> v
      | None ->
          let v = opt_nonrec opt p s in
          Hashtbl.add_exn tbl ~key ~data:v;
          v
    in
    opt

  let opt r = opt (Set.empty (module Name)) (Join_space.of_abslayout r)

  let transform =
    let f r =
      opt r
      |> Pareto_set.min_elt (fun a -> a.(0))
      |> Option.map ~f:mk_transform
      |> Option.bind ~f:(fun tf -> apply tf Path.root r)
    in
    local f "join-opt"
end

let%test_module _ =
  ( module struct
    module Config = struct
      let cost_conn = Db.create "postgresql:///tpch_1k"

      let conn = cost_conn

      let validate = false

      let param_ctx = Map.empty (module Name)

      let params = Set.empty (module Name)

      let simplify = None
    end

    module Join_opt = Make (Config)
    open Join_opt
    module M = Abslayout_db.Make (Config)

    let type_ = Type.PrimType.IntT { nullable = false }

    let c_custkey = Name.create ~type_ "c_custkey"

    let c_nationkey = Name.create ~type_ "c_nationkey"

    let n_nationkey = Name.create ~type_ "n_nationkey"

    let o_custkey = Name.create ~type_ "o_custkey"

    let orders = Db.relation Config.cost_conn "orders"

    let customer = Db.relation Config.cost_conn "customer"

    let nation = Db.relation Config.cost_conn "nation"

    let%expect_test "to-from-ralgebra" =
      let r =
        A.(
          join
            (Binop (Eq, Name c_nationkey, Name n_nationkey))
            (relation nation) (relation customer))
      in
      Join_space.of_abslayout r |> Join_space.to_ralgebra
      |> Format.printf "%a" Abslayout.pp;
      [%expect {|
    join((c_nationkey = n_nationkey), nation, customer) |}]

    let%expect_test "to-from-ralgebra" =
      let r =
        A.(
          join
            (Binop (Eq, Name c_custkey, Name o_custkey))
            (relation orders)
            (join
               (Binop (Eq, Name c_nationkey, Name n_nationkey))
               (relation nation) (relation customer)))
      in
      Join_space.of_abslayout r |> Join_space.to_ralgebra
      |> Format.printf "%a" Abslayout.pp;
      [%expect
        {|
    join((c_custkey = o_custkey),
      orders,
      join((c_nationkey = n_nationkey), nation, customer)) |}]

    let%expect_test "part-fold" =
      let r =
        A.(
          join
            (Binop (Eq, Name c_custkey, Name o_custkey))
            (relation orders)
            (join
               (Binop (Eq, Name c_nationkey, Name n_nationkey))
               (relation nation) (relation customer)))
      in
      let open Join_space in
      of_abslayout r
      |> partition_fold ~init:() ~f:(fun () (s1, s2, _) ->
             Format.printf "%a@.%a@.---\n" Abslayout.pp (to_ralgebra s1)
               Abslayout.pp (to_ralgebra s2));
      [%expect
        {|
    join((c_nationkey = n_nationkey), nation, customer)
    orders
    ---
    join((c_custkey = o_custkey), orders, customer)
    nation
    ---
    nation
    join((c_custkey = o_custkey), orders, customer)
    ---
    orders
    join((c_nationkey = n_nationkey), nation, customer)
    --- |}]

    let%expect_test "join-opt" =
      opt
        A.(
          join
            (Binop (Eq, Name c_nationkey, Name n_nationkey))
            (relation nation) (relation customer))
      |> [%sexp_of: (float array * t) list] |> print_s;
      [%expect
        {|
    (((998)
      (Flat
       ((node
         (Join
          ((pred
            (Binop
             (Eq (Name ((scope ()) (name c_nationkey)))
              (Name ((scope ()) (name n_nationkey))))))
           (r1
            ((node
              (Relation
               ((r_name customer)
                (r_schema
                 ((((scope ()) (name c_custkey)) ((scope ()) (name c_name))
                   ((scope ()) (name c_address)) ((scope ()) (name c_nationkey))
                   ((scope ()) (name c_phone)) ((scope ()) (name c_acctbal))
                   ((scope ()) (name c_mktsegment))
                   ((scope ()) (name c_comment))))))))
             (meta
              ((free ())
               (refcnt
                ((((scope ()) (name c_acctbal)) 1)
                 (((scope ()) (name c_address)) 1)
                 (((scope ()) (name c_comment)) 1)
                 (((scope ()) (name c_custkey)) 1)
                 (((scope ()) (name c_mktsegment)) 1)
                 (((scope ()) (name c_name)) 1)
                 (((scope ()) (name c_nationkey)) 2)
                 (((scope ()) (name c_phone)) 1)))))))
           (r2
            ((node
              (Relation
               ((r_name nation)
                (r_schema
                 ((((scope ()) (name n_nationkey)) ((scope ()) (name n_name))
                   ((scope ()) (name n_regionkey)) ((scope ()) (name n_comment))))))))
             (meta
              ((free ())
               (refcnt
                ((((scope ()) (name n_comment)) 1) (((scope ()) (name n_name)) 1)
                 (((scope ()) (name n_nationkey)) 2)
                 (((scope ()) (name n_regionkey)) 1))))))))))
        (meta
         ((free ())
          (refcnt
           ((((scope ()) (name c_acctbal)) 1) (((scope ()) (name c_address)) 1)
            (((scope ()) (name c_comment)) 1) (((scope ()) (name c_custkey)) 1)
            (((scope ()) (name c_mktsegment)) 1) (((scope ()) (name c_name)) 1)
            (((scope ()) (name c_nationkey)) 1) (((scope ()) (name c_phone)) 1)
            (((scope ()) (name n_comment)) 1) (((scope ()) (name n_name)) 1)
            (((scope ()) (name n_nationkey)) 1)
            (((scope ()) (name n_regionkey)) 1))))))))) |}]

    let%expect_test "join-opt" =
      opt
        A.(
          join
            (Binop (Eq, Name c_custkey, Name o_custkey))
            (relation orders)
            (join
               (Binop (Eq, Name c_nationkey, Name n_nationkey))
               (relation nation) (relation customer)))
      |> [%sexp_of: (float array * t) list] |> print_s;
      [%expect
        {|
    (((1000)
      (Flat
       ((node
         (Join
          ((pred
            (Binop
             (Eq (Name ((scope ()) (name c_custkey)))
              (Name ((scope ()) (name o_custkey))))))
           (r1
            ((node
              (Join
               ((pred
                 (Binop
                  (Eq (Name ((scope ()) (name c_nationkey)))
                   (Name ((scope ()) (name n_nationkey))))))
                (r1
                 ((node
                   (Relation
                    ((r_name customer)
                     (r_schema
                      ((((scope ()) (name c_custkey)) ((scope ()) (name c_name))
                        ((scope ()) (name c_address))
                        ((scope ()) (name c_nationkey))
                        ((scope ()) (name c_phone)) ((scope ()) (name c_acctbal))
                        ((scope ()) (name c_mktsegment))
                        ((scope ()) (name c_comment))))))))
                  (meta
                   ((free ())
                    (refcnt
                     ((((scope ()) (name c_acctbal)) 1)
                      (((scope ()) (name c_address)) 1)
                      (((scope ()) (name c_comment)) 1)
                      (((scope ()) (name c_custkey)) 2)
                      (((scope ()) (name c_mktsegment)) 1)
                      (((scope ()) (name c_name)) 1)
                      (((scope ()) (name c_nationkey)) 2)
                      (((scope ()) (name c_phone)) 1)))))))
                (r2
                 ((node
                   (Relation
                    ((r_name nation)
                     (r_schema
                      ((((scope ()) (name n_nationkey))
                        ((scope ()) (name n_name))
                        ((scope ()) (name n_regionkey))
                        ((scope ()) (name n_comment))))))))
                  (meta
                   ((free ())
                    (refcnt
                     ((((scope ()) (name n_comment)) 1)
                      (((scope ()) (name n_name)) 1)
                      (((scope ()) (name n_nationkey)) 2)
                      (((scope ()) (name n_regionkey)) 1))))))))))
             (meta
              ((free ())
               (refcnt
                ((((scope ()) (name c_acctbal)) 1)
                 (((scope ()) (name c_address)) 1)
                 (((scope ()) (name c_comment)) 1)
                 (((scope ()) (name c_custkey)) 2)
                 (((scope ()) (name c_mktsegment)) 1)
                 (((scope ()) (name c_name)) 1)
                 (((scope ()) (name c_nationkey)) 1)
                 (((scope ()) (name c_phone)) 1)
                 (((scope ()) (name n_comment)) 1) (((scope ()) (name n_name)) 1)
                 (((scope ()) (name n_nationkey)) 1)
                 (((scope ()) (name n_regionkey)) 1)))))))
           (r2
            ((node
              (Relation
               ((r_name orders)
                (r_schema
                 ((((scope ()) (name o_orderkey)) ((scope ()) (name o_custkey))
                   ((scope ()) (name o_orderstatus))
                   ((scope ()) (name o_totalprice))
                   ((scope ()) (name o_orderdate))
                   ((scope ()) (name o_orderpriority))
                   ((scope ()) (name o_clerk)) ((scope ()) (name o_shippriority))
                   ((scope ()) (name o_comment))))))))
             (meta
              ((free ())
               (refcnt
                ((((scope ()) (name o_clerk)) 1)
                 (((scope ()) (name o_comment)) 1)
                 (((scope ()) (name o_custkey)) 2)
                 (((scope ()) (name o_orderdate)) 1)
                 (((scope ()) (name o_orderkey)) 1)
                 (((scope ()) (name o_orderpriority)) 1)
                 (((scope ()) (name o_orderstatus)) 1)
                 (((scope ()) (name o_shippriority)) 1)
                 (((scope ()) (name o_totalprice)) 1))))))))))
        (meta
         ((free ())
          (refcnt
           ((((scope ()) (name c_acctbal)) 1) (((scope ()) (name c_address)) 1)
            (((scope ()) (name c_comment)) 1) (((scope ()) (name c_custkey)) 1)
            (((scope ()) (name c_mktsegment)) 1) (((scope ()) (name c_name)) 1)
            (((scope ()) (name c_nationkey)) 1) (((scope ()) (name c_phone)) 1)
            (((scope ()) (name n_comment)) 1) (((scope ()) (name n_name)) 1)
            (((scope ()) (name n_nationkey)) 1)
            (((scope ()) (name n_regionkey)) 1) (((scope ()) (name o_clerk)) 1)
            (((scope ()) (name o_comment)) 1) (((scope ()) (name o_custkey)) 1)
            (((scope ()) (name o_orderdate)) 1)
            (((scope ()) (name o_orderkey)) 1)
            (((scope ()) (name o_orderpriority)) 1)
            (((scope ()) (name o_orderstatus)) 1)
            (((scope ()) (name o_shippriority)) 1)
            (((scope ()) (name o_totalprice)) 1))))))))) |}]
  end )
