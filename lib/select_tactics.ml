open Core
open Castor
open Abslayout
open Collections

module Config = struct
  module type S = sig
    include Ops.Config.S

    include Abslayout_db.Config.S

    include Tactics_util.Config.S
  end
end

module Make (C : Config.S) = struct
  module Ops = Ops.Make (C)
  open Ops
  module M = Abslayout_db.Make (C)
  module U = Tactics_util.Make (C)
  open U

  let to_select r = match r.node with Select (p, r) -> Some (p, r) | _ -> None

  (** Extend a list of predicates to include those needed by aggregate `p`.
     Returns a name to use in the aggregate. *)
  let extend_aggs aggs p =
    let aggs = ref aggs in
    let add_agg a =
      match List.find !aggs ~f:(fun (_, a') -> [%compare.equal: pred] a a') with
      | Some (n, _) -> Name n
      | None ->
          let n =
            Fresh.name Global.fresh "agg%d"
            |> Name.create ~type_:(Pred.to_type a)
          in
          aggs := (n, a) :: !aggs;
          Name n
    in
    let visitor =
      object
        inherit [_] Abslayout0.map

        method! visit_Exists () r = Exists r

        method! visit_First () r = First r

        method! visit_Sum () p = Sum (add_agg (Sum p))

        method! visit_Count () = Sum (add_agg Count)

        method! visit_Min () p = Min (add_agg (Min p))

        method! visit_Max () p = Max (add_agg (Max p))

        method! visit_Avg () p =
          Binop (Div, Sum (add_agg (Sum p)), Sum (add_agg Count))
      end
    in
    let p' = visitor#visit_pred () p in
    (!aggs, p')

  (** Generate aggregates for collections that act by concatenating their
     children. *)
  let gen_concat_select_list outer_preds inner_schema =
    let outer_aggs, inner_aggs =
      (* Collect the aggregates that are supported by the inner relation. *)
      let inner_names = Set.of_list (module Name) inner_schema in
      List.fold_left outer_preds ~init:([], []) ~f:(fun (op, ip) p ->
          if is_supported inner_names p then
            let ip, p = extend_aggs ip p in
            (op @ [ p ], ip)
          else (op @ [ p ], ip))
    in
    let inner_aggs =
      List.map inner_aggs ~f:(fun (n, a) -> Pred.as_pred (a, Name.name n))
    in
    (* Don't want to project out anything that we might need later. *)
    let inner_fields = inner_schema |> List.map ~f:(fun n -> Name n) in
    (outer_aggs, inner_aggs @ inner_fields)

  (** Look for evidence of a previous pushed select. *)
  let already_pushed r' =
    try
      match Path.get_exn (Path.child Path.root 1) r' with
      | { node = Filter (_, { node = Select _; _ }); _ } -> true
      | _ -> false
    with _ -> false

  let push_select r =
    let open Option.Let_syntax in
    let%bind ps, r' = to_select r in
    if already_pushed r' then None
    else
      let%bind outer_preds, inner_preds =
        match r'.node with
        | AHashIdx { hi_values = rv; _ }
        | AOrderedIdx (_, rv, _)
        | AList (_, rv)
        | ATuple (rv :: _, Concat) ->
            let o, i = gen_concat_select_list ps (schema_exn rv) in
            Some (o, i)
        | _ -> None
      in
      let%map mk_collection =
        match r'.node with
        | AHashIdx h ->
            Some
              (fun mk_select ->
                hash_idx' { h with hi_values = mk_select h.hi_values })
        | AOrderedIdx (rk, rv, m) ->
            Some
              (fun mk_select -> ordered_idx rk (scope_exn rk) (mk_select rv) m)
        | AList (rk, rv) ->
            Some (fun mk_select -> list rk (scope_exn rk) (mk_select rv))
        | ATuple (r' :: rs', Concat) ->
            Some
              (fun mk_select ->
                tuple (List.map (r' :: rs') ~f:mk_select) Concat)
        | _ -> None
      in
      let count_n = Fresh.name Global.fresh "count%d" in
      let inner_preds = Pred.as_pred (Count, count_n) :: inner_preds in
      select outer_preds
        (mk_collection (fun rv ->
             filter
               (Binop (Gt, Name (Name.create count_n), Int 0))
               (select inner_preds rv)))

  let push_select = of_func push_select ~name:"push-select"
end

module Test = struct
  module C = struct
    let params =
      Set.of_list
        (module Name)
        [ Name.create ~type_:(DateT { nullable = false }) "param0" ]

    let simplify = None

    let fresh = Fresh.create ()

    let verbose = false

    let validate = false

    let param_ctx = Map.empty (module Name)

    let conn = Db.create "postgresql:///tpch_1k"

    let cost_conn = conn
  end

  module T = Make (C)
  module O = Ops.Make (C)
  module M = Abslayout_db.Make (C)
  open T

  let%expect_test "" =
    O.apply push_select Path.root
      (M.load_string
         {|
select([p_size * p_retailprice, p_retailprice * p_retailprice],
ahashidx(select([p_size], part) as k,
alist(filter(k.p_size = p_size, part) as k1, ascalar(k1.p_retailprice)), 0))
|})
    |> Option.iter ~f:(Format.printf "%a" Abslayout.pp);
    [%expect
      {|
      select([(p_size * p_retailprice), (p_retailprice * p_retailprice)],
        ahashidx(select([p_size], part) as k,
          filter((count0 > 0),
            select([count() as count0, p_retailprice],
              alist(filter((k.p_size = p_size), part) as k1,
                ascalar(k1.p_retailprice)))),
          0)) |}]

  let%expect_test "" =
    O.apply push_select Path.root
      (M.load_string
         {|
select([p_size * p_retailprice, p_retailprice * p_retailprice],
aorderedidx(select([p_size], part) as k,
alist(filter(k.p_size = p_size, part) as k1, ascalar(k1.p_retailprice)), 0, 1))
|})
    |> Option.iter ~f:(Format.printf "%a" Abslayout.pp);
    [%expect
      {|
      select([(p_size * p_retailprice), (p_retailprice * p_retailprice)],
        aorderedidx(select([p_size], part) as k,
          filter((count1 > 0),
            select([count() as count1, p_retailprice],
              alist(filter((k.p_size = p_size), part) as k1,
                ascalar(k1.p_retailprice)))),
          >= 0, < 1)) |}]

  let%expect_test "" =
    O.apply push_select Path.root
      (M.load_string
         {|
select([(select([min(o_totalprice)], orders)) * p_size * p_retailprice, p_retailprice * p_retailprice],
aorderedidx(select([p_size], part) as k,
alist(filter(k.p_size = p_size, part) as k1, ascalar(k1.p_retailprice)), 0, 1))
|})
    |> Option.iter ~f:(Format.printf "%a" Abslayout.pp);
    [%expect
      {|
      select([(((select([min(o_totalprice)], orders)) * p_size) * p_retailprice),
              (p_retailprice * p_retailprice)],
        aorderedidx(select([p_size], part) as k,
          filter((count2 > 0),
            select([count() as count2, p_retailprice],
              alist(filter((k.p_size = p_size), part) as k1,
                ascalar(k1.p_retailprice)))),
          >= 0, < 1)) |}]

  let%expect_test "" =
    O.apply push_select Path.root
      (M.load_string
         {|
select([sum((l_extendedprice * l_discount)) as revenue],
  aorderedidx(dedup(select([l_discount, l_quantity], lineitem)) as s1,
    select([l_extendedprice],
      alist(select([l_extendedprice], lineitem) as s2,
        ascalar(s2.l_extendedprice))),
    >= (0.01), <= (0.01), , < 1.0))|})
    |> Option.iter ~f:(Format.printf "%a" Abslayout.pp);
    [%expect
      {|
      select([sum((l_extendedprice * l_discount)) as revenue],
        aorderedidx(dedup(select([l_discount, l_quantity], lineitem)) as s1,
          filter((count3 > 0),
            select([count() as count3, l_extendedprice],
              select([l_extendedprice],
                alist(select([l_extendedprice], lineitem) as s2,
                  ascalar(s2.l_extendedprice))))),
          >= 0.01, <= 0.01, , < 1.0)) |}]
end
