open Base
open Castor
open Collections
module A = Abslayout
open Graph

module JoinGraph = struct
  module Vertex = struct
    include Abslayout

    let equal = [%compare.equal: t]
  end

  module Edge = struct
    include A.Pred

    let default = A.Bool true
  end

  module G = Persistent.Graph.ConcreteLabeled (Vertex) (Edge)
  include G
  include Oper.P (G)
  module Dfs = Traverse.Dfs (G)
  include Oper.Choose (G)

  let sexp_of_t g =
    fold_edges_e (fun e l -> e :: l) g []
    |> [%sexp_of: (Vertex.t * Edge.t * Vertex.t) list]

  let compare g1 g2 = Sexp.compare ([%sexp_of: t] g1) ([%sexp_of: t] g2)

  let add_or_update_edge g ((v1, l, v2) as e) =
    try
      let _, l', _ = find_edge g v1 v2 in
      add_edge_e g (v1, Binop (And, l, l'), v2)
    with Caml.Not_found -> add_edge_e g e

  let vertices g = fold_vertex (fun v l -> v :: l) g []

  let partition g vs =
    let g1, g2 =
      fold_vertex
        (fun v (lhs, rhs) ->
          let in_set = Set.mem vs v in
          let lhs = if in_set then remove_vertex lhs v else lhs in
          let rhs = if in_set then rhs else remove_vertex rhs v in
          (lhs, rhs) )
        g (g, g)
    in
    let es =
      fold_edges_e
        (fun ((v1, _, v2) as e) es ->
          if
            (Set.mem vs v1 && not (Set.mem vs v2))
            || ((not (Set.mem vs v1)) && Set.mem vs v2)
          then e :: es
          else es )
        g []
    in
    (g1, g2, es)

  let is_connected g =
    let n = nb_vertex g in
    let n = Dfs.fold_component (fun _ i -> i - 1) n g (choose_vertex g) in
    n = 0
end

let source_relation leaves n =
  let r_m =
    List.find_map leaves ~f:(fun (r, s) -> if Set.mem s n then Some r else None)
  in
  match r_m with
  | Some r -> r
  | None ->
      Error.(create "No source found for name." n [%sexp_of: Name.t] |> raise)

module JoinSpace = struct
  module T = struct
    type t =
      { graph: JoinGraph.t
      ; filters: Set.M(A.Pred).t
      ; leaves: (JoinGraph.Vertex.t * Set.M(Name).t) list }
    [@@deriving compare, sexp_of]
  end

  include T
  module C = Comparable.Make (T)

  module O : Comparable.Infix with type t := t = C

  let empty =
    {graph= JoinGraph.empty; filters= Set.empty (module A.Pred); leaves= []}

  let length {graph; _} = JoinGraph.nb_vertex graph

  let choose {graph; _} = JoinGraph.choose_vertex graph

  let contract join g =
    let open JoinGraph in
    (* if the edge is to be removed (property = true):
     * make a union of the two union-sets of start and end node;
     * put this set in the map for all nodes in this set *)
    let f edge m =
      let s_src, j_src = Map.find_exn m (E.src edge) in
      let s_dst, j_dst = Map.find_exn m (E.dst edge) in
      let s = Set.union s_src s_dst in
      let j = join ~label:(G.E.label edge) j_src j_dst in
      Set.fold
        ~f:(fun m vertex -> Map.set m ~key:vertex ~data:(s, j))
        s ~init:m
    in
    (* initialize map with singleton-sets for every node (of itself) *)
    let m =
      G.fold_vertex
        (fun vertex m ->
          Map.set m ~key:vertex
            ~data:(Set.singleton (module Vertex) vertex, vertex) )
        g
        (Map.empty (module Vertex))
    in
    G.fold_edges_e f g m |> Map.data |> List.hd_exn |> fun (_, j) -> j

  let to_ralgebra {graph; _} =
    if JoinGraph.nb_vertex graph = 1 then JoinGraph.choose_vertex graph
    else contract (fun ~label:p j1 j2 -> A.join p j1 j2) graph

  let of_abslayout r =
    let rec leaves r =
      let open A in
      match r.node with
      | Join {r1; r2; _} -> Set.union (leaves r1) (leaves r2)
      | Filter (_, r) -> leaves r
      | _ -> Set.singleton (module A) r
    in
    let leaves =
      leaves r |> Set.to_list
      |> List.map ~f:(fun r ->
             let s = Meta.(find_exn r schema) |> Set.of_list (module Name) in
             (r, s) )
    in
    (object (self : 'a)
       inherit [_] A.reduce

       method zero = empty

       method plus s1 s2 : t =
         { graph= JoinGraph.union s1.graph s2.graph
         ; filters= Set.union s1.filters s2.filters
         ; leaves=
             List.append s1.leaves s2.leaves
             |> List.dedup_and_sort ~compare:(fun (r1, _) (r2, _) ->
                    [%compare: A.t] r1 r2 ) }

       method! visit_Join () p r1 r2 =
         let s : t = self#plus (self#visit_t () r1) (self#visit_t () r2) in
         List.fold_left (A.Pred.conjuncts p) ~init:s ~f:(fun s p ->
             let pred_rels =
               List.map
                 (A.Pred.names p |> Set.to_list)
                 ~f:(source_relation leaves)
             in
             match pred_rels with
             | [r1; r2] ->
                 { s with
                   graph= JoinGraph.add_or_update_edge s.graph (r1, p, r2) }
             | _ ->
                 Logs.warn (fun m ->
                     m "Join-opt: Unhandled predicate %a" A.pp_pred p ) ;
                 s )

       method! visit_Filter () (p, r) : t =
         let s = self#visit_t () r in
         {s with filters= Set.add s.filters p}
    end)
      #visit_t () r

  let partition_fold ~init ~f {graph; filters; leaves} =
    let vertices = JoinGraph.vertices graph |> Array.of_list in
    let n = Array.length vertices in
    let rec loop acc k =
      if k >= n then acc
      else
        let acc =
          Combinat.Combination.fold (k, n) ~init:acc ~f:(fun acc vs ->
              let g1, g2, es =
                JoinGraph.partition graph
                  ( List.init k ~f:(fun i -> vertices.(vs.{i}))
                  |> Set.of_list (module JoinGraph.Vertex) )
              in
              if JoinGraph.is_connected g1 && JoinGraph.is_connected g2 then
                let s1 = {graph= g1; filters; leaves} in
                let s2 = {graph= g2; filters; leaves} in
                f acc (s1, s2, es)
              else acc )
        in
        loop acc (k + 1)
    in
    loop init 1
end

type t =
  | Flat of A.t
  | Hash of {lkey: A.pred; lhs: t; rkey: A.pred; rhs: t}
  | Nest of {lhs: t; rhs: t; pred: A.pred}
[@@deriving sexp_of]

type ctx = {sql: Sql.ctx; conn: Postgresql.connection; dbconn: Db.t}

let create_ctx sql conn dbconn = {sql; conn; dbconn}

(* let rec emit_joins = function
 *   | Flat r -> r
 *   | Hash {lkey; lhs; rkey; rhs} ->
 *       Option.value_exn
 *         (apply elim_join_hash Path.root
 *            (join (Binop (Eq, lkey, rkey)) (emit_joins lhs) (emit_joins rhs)))
 *   | Nest {lhs; rhs; pred} ->
 *       Option.value_exn
 *         (apply elim_join_nest Path.root
 *            (join pred (emit_joins lhs) (emit_joins rhs))) *)

let rec to_ralgebra = function
  | Flat r -> r
  | Nest {lhs; rhs; pred} -> A.join pred (to_ralgebra lhs) (to_ralgebra rhs)
  | Hash {lkey; rkey; lhs; rhs} ->
      A.join (Binop (Eq, lkey, rkey)) (to_ralgebra lhs) (to_ralgebra rhs)

module Cost = struct
  let read = function
    | Type.PrimType.(IntT _ | DateT _ | FixedT _ | StringT _) -> 4.0
    | BoolT _ -> 1.0
    | _ -> failwith "Unexpected type."

  let hash = function
    | Type.PrimType.(IntT _ | DateT _ | FixedT _ | BoolT _) -> 1.0
    | StringT _ -> 100.0
    | _ -> failwith "Unexpected type."

  let size = function
    | Type.PrimType.(IntT _ | DateT _ | FixedT _) -> 4.0
    | StringT _ -> 25.0
    | BoolT _ -> 1.0
    | _ -> failwith "Unexpected type."

  (* TODO: Not all lists have 16B headers *)
  let list_size = 16.0
end

let ntuples ctx r =
  let module M = Abslayout_db.Make (struct
    let conn = ctx.dbconn
  end) in
  let r = to_ralgebra r in
  M.annotate_schema r ;
  ( Explain.explain ctx.conn
      (Sql.of_ralgebra ctx.sql r |> Sql.to_string ctx.sql)
  |> Or_error.ok_exn )
    .nrows |> Float.of_int

let schema ctx r =
  let module M = Abslayout_db.Make (struct
    let conn = ctx.dbconn
  end) in
  M.annotate_schema r ;
  Meta.(find_exn r schema)

let schema_types ctx r = schema ctx r |> List.map ~f:Name.type_exn

let rec to_abslayout = function
  | Flat r -> r
  | Nest {lhs; rhs; pred} -> A.join pred (to_abslayout lhs) (to_abslayout rhs)
  | Hash {lkey; rkey; lhs; rhs} ->
      A.(join (Binop (And, lkey, rkey)) (to_abslayout lhs) (to_abslayout rhs))

let estimate_ntuples_parted ctx parts r =
  let module M = Abslayout_db.Make (struct
    let conn = ctx.dbconn
  end) in
  let s = schema ctx (to_ralgebra r) |> Set.of_list (module Name) in
  let parts =
    List.filter parts ~f:(fun (_, _, ns, _) -> Set.is_subset ns ~of_:s)
  in
  (* let all_tuples =
   *   List.fold_left parts ~init:a ~f:(fun j (d, _, _, p) ->
   *       if JoinGraph.Vertex.O.(a = d) then j else A.join p d j )
   * in *)
  let part_counts =
    A.(
      group_by
        [As_pred (Count, "c")]
        (List.concat_map parts ~f:(fun (_, _, ns, _) -> Set.to_list ns))
        (to_abslayout r))
  in
  let part_aggs =
    let c = A.(Name (Name.create "c")) in
    A.(select [Min c; Max c; Avg c] part_counts)
  in
  M.annotate_schema part_aggs ;
  let sql = Sql.of_ralgebra ctx.sql part_aggs in
  let tups =
    Db.exec_cursor_exn ctx.dbconn
      Type.PrimType.
        [ IntT {nullable= false}
        ; IntT {nullable= false}
        ; FixedT {nullable= false} ]
      (Sql.to_string ctx.sql sql)
  in
  match Gen.to_list tups with
  | [|Int min; Int max; Fixed avg|] :: _ -> (min, max, Fixed_point.to_float avg)
  | _ -> failwith "Unexpected tuples."

let to_parts ctx lhs rhs pred =
  let lhs_names, rhs_names =
    let lhs_schema = schema ctx lhs |> Set.of_list (module Name) in
    let rhs_schema = schema ctx rhs |> Set.of_list (module Name) in
    let pred_names =
      A.Pred.names pred
      |> Set.filter ~f:(fun n -> Set.mem lhs_schema n || Set.mem rhs_schema n)
    in
    Set.partition_tf pred_names ~f:(Set.mem lhs_schema)
  in
  (lhs, lhs_names, rhs_names, pred)

let rec estimate_cost ctx parts r =
  let sum = List.sum (module Float) in
  match r with
  | Flat _ ->
      let _, _, nt = estimate_ntuples_parted ctx parts r in
      let scan_cost =
        sum (schema_types ctx (to_ralgebra r)) ~f:Cost.read *. nt
      in
      let size_cost =
        (sum (schema_types ctx (to_ralgebra r)) ~f:Cost.size *. nt)
        +. Cost.list_size
      in
      [|size_cost; scan_cost|]
  | Nest {lhs; rhs; pred} ->
      let _, _, lhs_nt = estimate_ntuples_parted ctx parts lhs in
      let lhs_costs = estimate_cost ctx parts lhs in
      let lhs_size = lhs_costs.(0) in
      let lhs_scan = lhs_costs.(1) in
      let rhs_per_partition_costs =
        estimate_cost ctx
          (to_parts ctx (to_ralgebra lhs) (to_ralgebra rhs) pred :: parts)
          rhs
      in
      let size_cost = lhs_size +. (lhs_nt *. rhs_per_partition_costs.(0)) in
      let scan_cost = lhs_scan +. (lhs_nt *. rhs_per_partition_costs.(1)) in
      [|size_cost; scan_cost|]
  | Hash {lkey; lhs; rhs; rkey} ->
      let _, _, nt_lhs = estimate_ntuples_parted ctx parts lhs in
      let lhs_costs = estimate_cost ctx parts lhs in
      let lhs_size = lhs_costs.(0) in
      let lhs_scan = lhs_costs.(1) in
      let rhs_costs = estimate_cost ctx parts lhs in
      let rhs_size = rhs_costs.(0) in
      let rhs_per_partition_costs =
        let pred = A.(Binop (Eq, lkey, rkey)) in
        estimate_cost ctx
          (to_parts ctx (to_ralgebra lhs) (to_ralgebra rhs) pred :: parts)
          rhs
      in
      let size_cost = lhs_size +. rhs_size in
      let scan_cost =
        lhs_scan
        +. nt_lhs
           *. ( Cost.hash (Name.type_exn (A.pred_to_schema lkey))
              +. rhs_per_partition_costs.(1) )
      in
      [|size_cost; scan_cost|]

module ParetoSet = struct
  type 'a t = (float array * 'a) list

  let empty = []

  let singleton c v = [(c, v)]

  let dominates x y =
    assert (Array.length x = Array.length y) ;
    let n = Array.length x in
    let rec loop i le lt =
      if i = n then le && lt
      else
        loop (i + 1) Float.(le && x.(i) <= y.(i)) Float.(lt || x.(i) < y.(i))
    in
    loop 0 true false

  let rec add s c v =
    match s with
    | [] -> [(c, v)]
    | (c', v') :: s' ->
        if Array.(equal Float.( = ) c c') || dominates c' c then s
        else if dominates c c' then add s' c v
        else (c', v') :: add s' c v

  let of_list l = List.fold_left l ~init:[] ~f:(fun s (c, v) -> add s c v)

  let union_all ss = List.concat ss |> of_list
end

let opt ctx r =
  let rec opt ctx parts s =
    if JoinSpace.length s = 1 then
      let j = Flat (JoinSpace.choose s) in
      ParetoSet.singleton (estimate_cost ctx parts j) j
    else
      JoinSpace.partition_fold s ~init:ParetoSet.empty
        ~f:(fun cs (s1, s2, es) ->
          let pred = A.Pred.conjoin (List.map es ~f:(fun (_, p, _) -> p)) in
          (* Add flat joins to pareto set. *)
          let flat_joins =
            let select_flat s =
              List.filter_map (opt ctx parts s) ~f:(fun (_, j) ->
                  match j with Flat r -> Some r | _ -> None )
            in
            List.cartesian_product (select_flat s1) (select_flat s2)
            |> List.map ~f:(fun (r1, r2) ->
                   let j = Flat (A.join pred r1 r2) in
                   (estimate_cost ctx parts j, j) )
            |> ParetoSet.of_list
          in
          (* Add nest joins to pareto set. *)
          let nest_joins =
            let lhs_parts =
              to_parts ctx (JoinSpace.to_ralgebra s1)
                (JoinSpace.to_ralgebra s1) pred
              :: parts
            in
            let rhs_parts =
              to_parts ctx (JoinSpace.to_ralgebra s1)
                (JoinSpace.to_ralgebra s2) pred
              :: parts
            in
            let lhs_set =
              List.map (opt ctx lhs_parts s1) ~f:(fun (_, j) -> j)
            in
            let rhs_set =
              List.map (opt ctx rhs_parts s2) ~f:(fun (_, j) -> j)
            in
            List.cartesian_product lhs_set rhs_set
            |> List.map ~f:(fun (j1, j2) ->
                   let j = Nest {lhs= j1; rhs= j2; pred} in
                   (estimate_cost ctx parts j, j) )
            |> ParetoSet.of_list
          in
          (* Add hash joins to pareto set. *)
          let hash_joins =
            let lhs_schema =
              schema ctx (JoinSpace.to_ralgebra s1) |> Set.of_list (module Name)
            in
            let rhs_schema =
              schema ctx (JoinSpace.to_ralgebra s2) |> Set.of_list (module Name)
            in
            (* Figure out which partition a key comes from. *)
            let key_side k =
              let rs = A.Pred.names k |> Set.to_list in
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
                  if JoinSpace.O.(s1 = s2) then []
                  else
                    let rhs_parts =
                      to_parts ctx (JoinSpace.to_ralgebra s1)
                        (JoinSpace.to_ralgebra s2) pred
                      :: parts
                    in
                    List.cartesian_product (opt ctx parts s1)
                      (opt ctx rhs_parts s2)
                    |> List.map ~f:(fun ((_, r1), (_, r2)) ->
                           Hash {lkey= k1; rkey= k2; lhs= r1; rhs= r2} )
              | _ -> None
            in
            Option.value m_s ~default:[]
            |> List.map ~f:(fun j -> (estimate_cost ctx parts j, j))
          in
          ParetoSet.union_all [cs; flat_joins; nest_joins; hash_joins] )
  in
  let module M = Abslayout_db.Make (struct
    let conn = ctx.dbconn
  end) in
  M.annotate_schema r ;
  opt ctx [] (JoinSpace.of_abslayout r)