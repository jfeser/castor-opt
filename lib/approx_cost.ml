open! Core
open! Castor
module A = Abslayout

module Config = struct
  module type S = sig
    val conn : Db.t

    val cost_conn : Db.t
  end
end

module Make (C : Config.S) = struct
  open C

  module Scope = struct
    module T = struct
      type t = (A.t * string) list [@@deriving compare, hash, sexp_of]
    end

    include T
    include Comparator.Make (T)
  end

  type t = Pred.t Map.M(Name).t Hashtbl.M(Scope).t

  let cache = Hashtbl.create (module Scope)

  let () = Hashtbl.set cache ~key:[] ~data:[ Map.empty (module Name) ]

  let find ctx =
    match Hashtbl.find cache ctx with
    | Some x -> x
    | None ->
        let ret =
          let rec query ss = function
            | [] -> assert false
            | [ (q, _) ] ->
                A.select
                  (ss @ List.map (A.schema_exn q) ~f:(fun n -> A.Name n))
                  q
            | (q, s) :: qs ->
                A.dep_join q s
                  (query
                     ( ss
                     @ List.map (A.schema_exn q) ~f:(fun n ->
                           A.Name (Name.copy ~scope:(Some s) n)) )
                     qs)
          in
          let schema =
            List.concat_map ctx ~f:(fun (q, s) ->
                List.map (A.schema_exn q) ~f:(Name.copy ~scope:(Some s)))
          in
          let q = query [] ctx in
          Sql.sample 10 (Sql.of_ralgebra q |> Sql.to_string)
          |> Db.exec_cursor_exn conn
               (Schema.schema_exn q |> List.map ~f:Name.type_exn)
          |> Gen.to_list
          |> List.map ~f:(fun vs ->
                 Array.to_list vs |> List.map ~f:Value.to_pred
                 |> List.zip_exn schema
                 |> Map.of_alist_exn (module Name))
        in
        Hashtbl.set cache ~key:ctx ~data:ret;
        ret

  class ntuples =
    object (self : 'a)
      inherit [_] A.reduce

      inherit [_] Util.float_sum_monoid

      method ntuples ctx q =
        let mean l =
          let n = List.sum (module Int) ~f:Fun.id l |> Float.of_int in
          let d = List.length l |> Float.of_int in
          let m = n /. d in
          if Float.is_nan m then 1.0 else m
        in
        List.map (find ctx) ~f:(fun subst ->
            let ntuples_query =
              A.subst subst q
              |> A.select [ Count ]
              |> Sql.of_ralgebra |> Sql.to_string
            in
            Log.debug (fun m -> m "Computing ntuples: %s" ntuples_query);
            Db.exec1 conn ntuples_query |> List.hd_exn |> Int.of_string)
        |> mean

      method! visit_AScalar _ _ = 1.0

      method! visit_ATuple ctx (ts, kind) =
        match kind with
        | Concat -> List.sum (module Float) ~f:(self#visit_t ctx) ts
        | Cross ->
            List.fold_left ~init:1.0 ~f:(fun x q -> x *. self#visit_t ctx q) ts
        | Zip ->
            List.fold_left ~init:1.0
              ~f:(fun x q -> Float.max x (self#visit_t ctx q))
              ts

      method! visit_AList ctx (lk, lv) =
        let lk, s = (A.strip_scope lk, A.scope_exn lk) in
        self#ntuples ctx lk *. self#visit_t (ctx @ [ (lk, s) ]) lv

      method! visit_AHashIdx ctx h =
        self#visit_t (ctx @ [ (h.hi_keys, h.hi_scope) ]) h.hi_values

      method! visit_AOrderedIdx ctx (lk, lv, _) =
        let lk, s = (A.strip_scope lk, A.scope_exn lk) in
        self#visit_t (ctx @ [ (lk, s) ]) lv

      method! visit_Join ctx j = self#visit_t ctx j.r1 *. self#visit_t ctx j.r2

      method! visit_Relation _ r =
        Db.relation_count conn r.r_name |> Float.of_int
    end

  let cost q =
    let c = (new ntuples)#visit_t [] q in
    Log.debug (fun m -> m "Got cost %f for: %a" c A.pp q);
    c
end

let%test_module _ =
  ( module struct
    module Config = struct
      let cost_conn = Db.create "postgresql:///tpch"

      let conn = cost_conn

      let simplify = None
    end

    module C = Make (Config)
    open C
    module M = Abslayout_db.Make (Config)

    let%expect_test "" =
      let q =
        {|
      alist(alist(dedup(
                                     select([r_name, ps_partkey],
                                       join((s_suppkey = ps_suppkey),
                                         join((s_nationkey = n_nationkey),
                                           join((n_regionkey = r_regionkey), nation, region),
                                           supplier),
                                         partsupp))) as k2,
                               select([r_name, ps_partkey, min(ps_supplycost) as min_cost],
                                 filter(((r_name = k2.r_name) && (ps_partkey = k2.ps_partkey)),
                                   join((s_suppkey = ps_suppkey),
                                     join((s_nationkey = n_nationkey),
                                       join((n_regionkey = r_regionkey), nation, region),
                                       supplier),
                                     partsupp)))) as s1,
                         atuple([ascalar(s1.r_name), ascalar(s1.ps_partkey), ascalar(s1.min_cost)], cross))

|}
        |> M.load_string
      in
      cost q |> printf "%f";
      [%expect {| 590143.000000 |}]
  end )
