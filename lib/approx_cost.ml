open! Core
open! Lwt
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

  type t = Pred.t Map.M(Name).t option Hashtbl.M(Scope).t

  let cache = Hashtbl.create (module Scope)

  let () = Hashtbl.set cache ~key:[] ~data:(Some [ Map.empty (module Name) ])

  let find ctx =
    match Hashtbl.find cache ctx with
    | Some x -> return x
    | None ->
        let rec query ss = function
          | [] -> assert false
          | [ (q, _) ] ->
              A.select (ss @ List.map (A.schema_exn q) ~f:(fun n -> A.Name n)) q
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
        let sample_query = Sql.sample 10 (Sql.of_ralgebra q |> Sql.to_string) in
        let%lwt samples =
          Db.exec_cursor_lwt_exn ~timeout:10.0 conn
            (Schema.schema_exn q |> List.map ~f:Name.type_exn)
            sample_query
            (fun tups ->
              Lwt_stream.filter_map Result.ok tups |> Lwt_stream.to_list)
        in
        if samples = [] then (
          Hashtbl.set cache ~key:ctx ~data:None;
          return None )
        else
          let substs =
            List.map samples ~f:(fun vs ->
                Array.to_list vs |> List.map ~f:Value.to_pred
                |> List.zip_exn schema
                |> Map.of_alist_exn (module Name))
          in
          Hashtbl.set cache ~key:ctx ~data:(Some substs);
          return (Some substs)

  class ntuples =
    object (self : 'a)
      inherit [_] A.reduce

      method zero = return 0.0

      method plus x y =
        let%lwt x = x in
        let%lwt y = y in
        return (x +. y)

      method mul x y =
        let%lwt x = x in
        let%lwt y = y in
        return (x *. y)

      method ntuples ctx q =
        let mean l =
          let n = List.sum (module Int) ~f:Fun.id l |> Float.of_int in
          let d = List.length l |> Float.of_int in
          if d = 0.0 then Float.infinity else n /. d
        in
        let%lwt substs = find ctx in
        match substs with
        | Some ss ->
            let%lwt counts =
              Lwt_list.map_p
                (fun subst ->
                  let ntuples_query =
                    A.subst subst q
                    |> A.select [ Count ]
                    |> Sql.of_ralgebra |> Sql.to_string
                  in
                  (* Log.debug (fun m -> m "Computing ntuples: %s" ntuples_query); *)
                  let%lwt count =
                    Db.exec_cursor_lwt_exn ~timeout:5.0 conn
                      [ Type.PrimType.int_t ] ntuples_query (fun count_tuples ->
                        Lwt_stream.get count_tuples)
                  in
                  match count with
                  | Some (Ok [| Int c |]) -> return (Some c)
                  | Some (Error _) -> return None
                  | _ -> assert false)
                ss
            in
            let counts = List.filter_map counts ~f:Fun.id in
            return @@ mean counts
        | None -> return Float.infinity

      method! visit_AScalar _ _ = return 1.0

      method! visit_ATuple ctx (ts, kind) =
        match kind with
        | Concat ->
            List.map ts ~f:(self#visit_t ctx)
            |> List.fold_left ~init:self#zero ~f:self#plus
        | Cross ->
            List.map ts ~f:(self#visit_t ctx)
            |> List.fold_left ~init:(return 1.0) ~f:self#mul
        | Zip -> failwith "unsupported"

      method! visit_AList ctx (lk, lv) =
        let lk, s = (A.strip_scope lk, A.scope_exn lk) in
        self#mul (self#ntuples ctx lk) (self#visit_t (ctx @ [ (lk, s) ]) lv)

      method! visit_AHashIdx ctx h =
        self#visit_t (ctx @ [ (h.hi_keys, h.hi_scope) ]) h.hi_values

      method! visit_AOrderedIdx ctx (lk, lv, _) =
        let lk, s = (A.strip_scope lk, A.scope_exn lk) in
        self#visit_t (ctx @ [ (lk, s) ]) lv

      method! visit_Join ctx j =
        self#mul (self#visit_t ctx j.r1) (self#visit_t ctx j.r2)

      method! visit_Relation _ r =
        Db.relation_count conn r.r_name |> Float.of_int |> return
    end

  let cost q =
    let c = (new ntuples)#visit_t [] q |> Lwt_main.run in
    (* Log.debug (fun m -> m "Got cost %f for: %a" c A.pp q); *)
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
      [%expect {| inf |}]
  end )
