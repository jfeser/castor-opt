open! Core
open! Lwt
open! Castor
open Collections
module A = Abslayout

module Config = struct
  module type S = sig
    val conn : Db.t

    val cost_conn : Db.t

    val params : Set.M(Name).t
  end
end

module Make (C : Config.S) = struct
  open C

  let conn = cost_conn

  module Scope = struct
    module T = struct
      type t = (A.t * string) list [@@deriving compare, hash, sexp_of]
    end

    include T
    include Comparator.Make (T)
  end

  let exec ?timeout db schema sql =
    Db.exec_lwt_exn ?timeout db schema sql
    |> Lwt_stream.filter_map (function
         | Ok t -> Some t
         | Error `Timeout -> None
         | Error (`Exn e) -> raise e)
    |> Lwt_stream.to_list

  let sample_single ?(n = 3) conn q s =
    let schema = A.schema_exn q in
    let fetch_sample sql =
      exec ~timeout:60.0 conn
        (Schema.schema_exn q |> List.map ~f:Name.type_exn)
        sql
    in
    let sql =
      A.select (List.map (A.schema_exn q) ~f:(fun n -> A.Name n)) q
      |> Sql.of_ralgebra |> Sql.to_string
    in
    let%lwt samples = fetch_sample @@ Sql.sample n sql in
    let%lwt samples =
      if samples = [] then fetch_sample @@ Sql.trash_sample n sql
      else return samples
    in
    if samples = [] then return None
    else
      let substs =
        List.map samples ~f:(fun vs ->
            Array.to_list vs |> List.map ~f:Value.to_pred
            |> List.zip_exn (List.map schema ~f:(Name.scoped s))
            |> Map.of_alist_exn (module Name))
      in
      return (Some substs)

  (** Sample n tuples from a context. *)
  let sample =
    let rec sample n = function
      | [] -> return (Some [ Map.empty (module Name) ])
      | (q, s) :: ss -> (
          let%lwt substs = sample_single conn q s in
          match substs with
          | Some substs ->
              let%lwt samples =
                Lwt_list.map_p
                  (fun subst ->
                    let%lwt samples =
                      List.map ss ~f:(fun (q, s) -> (A.subst subst q, s))
                      |> sample n
                    in
                    return
                    @@ Option.map samples ~f:(List.map ~f:(Map.merge_exn subst)))
                  substs
              in
              let samples =
                List.filter_map samples ~f:Fun.id |> List.concat |> List.permute
              in
              let samples = List.take samples n in
              if samples = [] then return None else return (Some samples)
          | None -> return None )
    in
    let memo = Memo.general (fun (n, ctx) -> sample n ctx) in
    fun ?(n = 3) ctx -> memo (n, ctx)

  (** Estimate the number of tuples returned by a query q. *)
  let ntuples ctx q =
    let mean l =
      let n = List.sum (module Int) ~f:Fun.id l |> Float.of_int in
      let d = List.length l |> Float.of_int in
      if d = 0.0 then Float.infinity else n /. d
    in
    let timeout = 10.0 *. (1.0 +. (List.length ctx |> Float.of_int)) in
    let%lwt substs = sample ctx in
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
                exec ~timeout conn [ Type.PrimType.int_t ] ntuples_query
              in
              match count with
              | [] -> return None
              | [| Int c |] :: _ -> return (Some c)
              | _ -> failwith "Unexpected tuples.")
            ss
        in
        let counts = List.filter_map counts ~f:Fun.id in
        return @@ mean counts
    | None -> return Float.infinity

  class ntuples_cost =
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
        self#mul (ntuples ctx lk) (self#visit_t (ctx @ [ (lk, s) ]) lv)

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

  class cpu_cost ntuples_cost =
    object (self : 'a)
      inherit [_] A.reduce as super

      method zero = return 0.0

      method plus x y =
        let%lwt x = x in
        let%lwt y = y in
        return (x +. y)

      method mul x y =
        let%lwt x = x in
        let%lwt y = y in
        return (x *. y)

      method! visit_Substring ctx p1 p2 p3 =
        self#plus (super#visit_Substring ctx p1 p2 p3) (return 20.0)

      method! visit_Binop ctx (op, p1, p2) =
        self#plus
          (super#visit_Binop ctx (op, p1, p2))
          (match op with Strpos -> return 20.0 | _ -> return 0.0)

      method! visit_First ctx r = self#visit_t ctx r

      method! visit_Exists ctx r = self#visit_t ctx r

      method! visit_AScalar ctx p =
        let%lwt c = self#visit_pred ctx p in
        return (max c 1.0)

      method! visit_ATuple ctx (ts, kind) =
        match kind with
        | Concat ->
            List.map ts ~f:(self#visit_t ctx)
            |> List.fold_left ~init:self#zero ~f:self#plus
        | Cross ->
            let _, c =
              List.map ts ~f:(fun r ->
                  (ntuples_cost#visit_t ctx r, self#visit_t ctx r))
              |> List.fold_left
                   ~init:(return 1.0, return 0.0)
                   ~f:
                     (fun (total_tuples, total_cost) (this_tuples, this_cost) ->
                     let n = self#mul total_tuples this_tuples in
                     let c =
                       self#plus total_cost (self#mul total_tuples this_cost)
                     in
                     (n, c))
            in
            c
        | Zip -> failwith "unsupported"

      method! visit_AList ctx (lk, lv) =
        let lk, s = (A.strip_scope lk, A.scope_exn lk) in
        self#mul (ntuples ctx lk) (self#visit_t (ctx @ [ (lk, s) ]) lv)

      method! visit_AHashIdx ctx h =
        let key_read_cost =
          List.length @@ A.schema_exn h.hi_keys |> Float.of_int |> return
        in
        let lookup_cost =
          if List.length h.hi_lookup = 1 then return 1.0 else return 10.0
        in
        self#plus key_read_cost @@ self#plus lookup_cost
        @@ self#visit_t (ctx @ [ (h.hi_keys, h.hi_scope) ]) h.hi_values

      method! visit_AOrderedIdx ctx (lk, lv, _) =
        let lk, s = (A.strip_scope lk, A.scope_exn lk) in
        let key_read_cost =
          List.length @@ A.schema_exn lk |> Float.of_int |> return
        in
        self#plus key_read_cost (self#visit_t (ctx @ [ (lk, s) ]) lv)

      method! visit_Join ctx j =
        self#plus (self#visit_t ctx j.r1)
          (self#mul (ntuples_cost#visit_t ctx j.r1) (self#visit_t ctx j.r2))

      method! visit_DepJoin ctx j =
        self#plus (self#visit_t ctx j.d_lhs)
          (self#mul
             (ntuples_cost#visit_t ctx j.d_lhs)
             (self#visit_t ctx j.d_rhs))

      method! visit_Relation = ntuples_cost#visit_Relation
    end

  let cost q =
    let cost = (new cpu_cost (new ntuples_cost))#visit_t [] q |> Lwt_main.run in
    (* Log.debug (fun m -> m "Cost %f for: %a" cost Abslayout.pp q); *)
    cost
end

let%test_module _ =
  ( module struct
    module Config = struct
      let conn = Db.create "postgresql:///tpch"

      let cost_conn = Db.create "postgresql:///tpch"

      let simplify = None

      let params = Set.empty (module Name)
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
