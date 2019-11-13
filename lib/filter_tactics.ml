open Core
open Castor
open Abslayout
open Collections

module Config = struct
  module type My_S = sig
    val params : Set.M(Name).t
  end

  module type S = sig
    include Ops.Config.S

    include Simplify_tactic.Config.S

    include Tactics_util.Config.S

    include My_S
  end
end

module Make (C : Config.S) = struct
  module O = Ops.Make (C)
  module S = Simplify_tactic.Make (C)
  open O
  open S
  module Tactics_util = Tactics_util.Make (C)

  module My_C : Config.My_S = C

  open My_C

  let schema_set_exn r = schema_exn r |> Set.of_list (module Name)

  (** Split predicates that sit under a binder into the parts that depend on
       bound variables and the parts that do not. *)
  let split_bound binder p =
    List.partition_tf (Pred.conjuncts p) ~f:(fun p' ->
        overlaps (pred_free p') (schema_set_exn binder))

  (** Check that a predicate is supported by a relation (it does not depend on
     anything in the context that it did not previously depend on.) *)
  let invariant_support orig_bound new_bound pred =
    let supported = Set.inter (pred_free pred) orig_bound in
    Set.is_subset supported ~of_:new_bound

  let to_filter r = match r.node with Filter (p, r) -> Some (p, r) | _ -> None

  let merge_select s1 s2 =
    s1 @ s2
    |> List.dedup_and_sort ~compare:(fun p1 p2 ->
           [%compare: Name.t option] (Schema.to_name p1) (Schema.to_name p2))

  let hoist_filter r =
    let open Option.Let_syntax in
    match r.node with
    | OrderBy { key; rel } ->
        let%map p, r = to_filter rel in
        filter p (order_by key r)
    | GroupBy (ps, key, r) ->
        let%bind p, r = to_filter r in
        if
          invariant_support (schema_set_exn r)
            (schema_set_exn (group_by ps key r))
            p
        then Some (filter p (group_by ps key r))
        else None
    | Filter (p', r) ->
        let%map p, r = to_filter r in
        filter (Binop (And, p, p')) r
    | Select (ps, r) -> (
        let%bind p, r = to_filter r in
        match select_kind ps with
        | `Scalar ->
            if Tactics_util.select_contains (pred_free p) ps r then
              Some (filter p (select ps r))
            else None
        | `Agg -> None )
    | Join { pred; r1; r2 } -> (
        match (to_filter r1, to_filter r2) with
        | Some (p1, r1), Some (p2, r2) ->
            Some (filter (Pred.conjoin [ p1; p2 ]) (join pred r1 r2))
        | None, Some (p, r2) -> Some (filter p (join pred r1 r2))
        | Some (p, r1), None -> Some (filter p (join pred r1 r2))
        | None, None -> None )
    | Dedup r ->
        let%map p, r = to_filter r in
        filter p (dedup r)
    | AList (rk, rv) ->
        let%map p, r = to_filter rv in
        filter (Pred.unscoped (scope_exn rk) p) (list rk (scope_exn rk) r)
    | AHashIdx ({ hi_keys = rk; hi_values = rv; _ } as h) ->
        let%map p, r = to_filter rv in
        let below, above = split_bound rk p in
        let above = List.map above ~f:(Pred.unscoped h.hi_scope) in
        filter (Pred.conjoin above)
          (hash_idx' { h with hi_values = filter (Pred.conjoin below) r })
    | AOrderedIdx (rk, rv, m) ->
        let%map p, r = to_filter rv in
        let below, above = split_bound rk p in
        let above = List.map above ~f:(Pred.unscoped (scope_exn rk)) in
        filter (Pred.conjoin above)
          (ordered_idx rk (scope_exn rk) (filter (Pred.conjoin below) r) m)
    | DepJoin { d_lhs; d_alias; d_rhs } ->
        let%map p, r = to_filter d_rhs in
        (* Ensure all the required names are selected. *)
        let select_list =
          let lhs_schema = schema_exn d_lhs in
          let lhs_select =
            lhs_schema |> Schema.to_select_list
            |> List.map ~f:(Pred.scoped lhs_schema d_alias)
          in
          let rhs_select = schema_exn d_rhs |> Schema.to_select_list in
          merge_select lhs_select rhs_select
        in
        filter (Pred.unscoped d_alias p)
          (dep_join d_lhs d_alias (select select_list r))
    | Relation _ | AEmpty | AScalar _ | ATuple _ | As (_, _) | Range _ -> None

  let hoist_filter = of_func hoist_filter ~name:"hoist-filter"

  let split_filter r =
    match r.node with
    | Filter (Binop (And, p, p'), r) -> Some (filter p (filter p' r))
    | _ -> None

  let split_filter = of_func split_filter ~name:"split-filter"

  let rec first_ok = function
    | Ok x :: _ -> Some x
    | _ :: xs -> first_ok xs
    | [] -> None

  let qualify rn p =
    let visitor =
      object
        inherit [_] Abslayout.endo

        method! visit_Name () _ n = Name (Name.copy ~scope:(Some rn) n)
      end
    in
    visitor#visit_pred () p

  let gen_ordered_idx ?lb ?ub p rk rv =
    let k = Fresh.name Global.fresh "k%d" in
    let n = Fresh.name Global.fresh "x%d" in
    ordered_idx
      (dedup (select [ Pred.as_pred (p, n) ] rk))
      k
      (filter (Binop (Eq, Name (Name.create ~scope:k n), p)) rv)
      { oi_key_layout = None; oi_lookup = [ (lb, ub) ] }

  (** A predicate `p` is a candidate lookup key into a partitioning of `r` if it
     does not depend on any of the fields in `r`.

      TODO: In practice we also want it to have a parameter in it. Is this correct? *)
  let is_candidate_key p r =
    let pfree = pred_free p in
    (not (overlaps (schema_set_exn r) pfree)) && overlaps params pfree

  (** A predicate is a candidate to be matched if all its free variables are
     bound by the relation that it is above. *)
  let is_candidate_match p r =
    Set.is_subset (pred_free p) ~of_:(schema_set_exn r)

  let elim_cmp_filter r =
    match r.node with
    | Filter (p, r') -> (
        (* Select the comparisons which have a parameter on exactly one side and
           partition by the unparameterized side of the comparison. *)
        let cmps, rest =
          Pred.conjuncts p
          |> List.partition_map ~f:(function
               | (Binop (Gt, p1, p2) | Binop (Lt, p2, p1)) as p ->
                   if is_candidate_key p1 r' && is_candidate_match p2 r' then
                     `Fst (p2, (`Lt, p1))
                   else if is_candidate_key p2 r' && is_candidate_match p1 r'
                   then `Fst (p1, (`Gt, p2))
                   else `Snd p
               | (Binop (Ge, p1, p2) | Binop (Le, p2, p1)) as p ->
                   if is_candidate_key p1 r' && is_candidate_match p2 r' then
                     `Fst (p2, (`Le, p1))
                   else if is_candidate_key p2 r' && is_candidate_match p1 r'
                   then `Fst (p1, (`Ge, p2))
                   else `Snd p
               | p -> `Snd p)
        in
        let cmps, rest' =
          Map.of_alist_multi (module Pred) cmps
          |> Map.to_alist
          |> List.map ~f:(fun (key, bounds) ->
                 let lb, rest =
                   let open_lb =
                     List.filter_map bounds ~f:(fun (f, p) ->
                         match f with `Gt -> Some p | _ -> None)
                   in
                   let closed_lb =
                     List.filter_map bounds ~f:(fun (f, p) ->
                         match f with `Ge -> Some p | _ -> None)
                   in
                   match
                     (List.length open_lb = 0, List.length closed_lb = 0)
                   with
                   | true, true -> (None, [])
                   | _, true ->
                       ( Option.map (List.reduce ~f:Pred.max_of open_lb)
                           ~f:(fun max -> (max, `Open)),
                         [] )
                   | _ ->
                       ( Option.map
                           (List.reduce ~f:Pred.max_of (open_lb @ closed_lb))
                           ~f:(fun max -> (max, `Closed)),
                         List.map open_lb ~f:(fun p -> Pred.binop (Gt, key, p))
                       )
                 in
                 let ub, rest' =
                   let open_ub =
                     List.filter_map bounds ~f:(fun (f, p) ->
                         match f with `Lt -> Some p | _ -> None)
                   in
                   let closed_ub =
                     List.filter_map bounds ~f:(fun (f, p) ->
                         match f with `Le -> Some p | _ -> None)
                   in
                   match
                     (List.length open_ub = 0, List.length closed_ub = 0)
                   with
                   | true, true -> (None, [])
                   | _, true ->
                       ( Option.map (List.reduce ~f:Pred.min_of open_ub)
                           ~f:(fun p -> (p, `Open)),
                         [] )
                   | _ ->
                       ( Option.map
                           (List.reduce ~f:Pred.min_of (open_ub @ closed_ub))
                           ~f:(fun p -> (p, `Closed)),
                         List.map open_ub ~f:(fun p -> Pred.binop (Gt, key, p))
                       )
                 in
                 ((key, (lb, ub)), rest @ rest'))
          |> List.unzip
        in
        let rest = rest @ List.concat rest' in
        let key, cmps = List.unzip cmps in
        let x =
          let open Or_error.Let_syntax in
          if key = [] then Or_error.error_string "No candidate keys found."
          else
            let%map all_keys = Tactics_util.all_values key r' in
            let scope = Fresh.name Global.fresh "s%d" in
            ordered_idx all_keys scope
              (Tactics_util.select_out (schema_exn all_keys)
                 (filter
                    ( List.map key ~f:(fun p ->
                          Pred.binop
                            (Eq, p, Pred.scoped (schema_exn all_keys) scope p))
                    |> Pred.conjoin )
                    r'))
              { oi_key_layout = None; oi_lookup = cmps }
        in
        match x with
        | Ok r -> Seq.singleton (filter (Pred.conjoin rest) r)
        | Error err ->
            Logs.warn (fun m -> m "Elim-cmp: %a" Error.pp err);
            Seq.empty )
    | _ -> Seq.empty

  let elim_cmp_filter =
    Branching.(local elim_cmp_filter ~name:"elim-cmp-filter")

  let push_filter_cross_tuple p rs =
    let ps = Pred.conjuncts p in
    (* Find the earliest placement for each predicate. *)
    let preds = Array.create ~len:(List.length rs) [] in
    let rec place_all ps i =
      if i >= List.length rs then ps
      else
        let bnd =
          List.nth_exn rs i |> schema_exn |> Set.of_list (module Name)
        in
        let pl, up = List.partition_tf ps ~f:(Tactics_util.is_supported bnd) in
        preds.(i) <- pl;
        place_all up (i + 1)
    in
    let rest = place_all ps 0 in
    let rs = List.mapi rs ~f:(fun i -> filter (Pred.conjoin preds.(i))) in
    filter (Pred.conjoin rest) (tuple rs Cross)

  let push_filter_list p rk rv =
    let scope = scope_exn rk in
    let rk = strip_scope rk in
    let rk_bnd = Set.of_list (module Name) (schema_exn rk) in
    let pushed_key, pushed_val =
      Pred.conjuncts p
      |> List.partition_map ~f:(fun p ->
             if Tactics_util.is_supported rk_bnd p then `Fst p else `Snd p)
    in
    let inner_key_pred = Pred.conjoin pushed_key in
    let inner_val_pred = Pred.conjoin pushed_val in
    list (filter inner_key_pred rk) scope (filter inner_val_pred rv)

  let push_filter_select p ps r =
    match select_kind ps with
    | `Scalar ->
        let ctx =
          List.filter_map ps ~f:(fun p ->
              Option.map (Pred.to_name p) ~f:(fun n -> (n, Pred.remove_as p)))
          |> Map.of_alist_exn (module Name)
        in
        let p' = Pred.subst ctx p in
        select ps (filter p' r)
    | `Agg ->
        let scalar_ctx =
          List.filter_map ps ~f:(fun p ->
              if Pred.kind p = `Scalar then
                Option.map (Pred.to_name p) ~f:(fun n -> (n, Pred.remove_as p))
              else None)
          |> Map.of_alist_exn (module Name)
        in
        let names = Map.keys scalar_ctx |> Set.of_list (module Name) in
        let pushed, unpushed =
          Pred.conjuncts p
          |> List.partition_map ~f:(fun p ->
                 if Tactics_util.is_supported names p then
                   `Fst (Pred.subst scalar_ctx p)
                 else `Snd p)
        in
        filter (Pred.conjoin unpushed)
          (select ps (filter (Pred.conjoin pushed) r))

  let push_filter r =
    let open Option.Let_syntax in
    let%bind p, r = to_filter r in
    match r.node with
    | Filter (p', r') -> Some (filter (Binop (And, p, p')) r')
    | Dedup r' -> Some (dedup (filter p r'))
    | Select (ps, r) -> Some (push_filter_select p ps r)
    | ATuple (rs, Concat) -> Some (tuple (List.map rs ~f:(filter p)) Concat)
    | ATuple (rs, Cross) -> Some (push_filter_cross_tuple p rs)
    (* Lists are a special case because their keys are bound at compile time and
       are not available at runtime. *)
    | AList (rk, rv) -> Some (push_filter_list p rk rv)
    | _ ->
        let%map rk, scope, rv, mk =
          match r.node with
          | DepJoin { d_lhs = rk; d_rhs = rv; d_alias } ->
              Some (rk, d_alias, rv, dep_join)
          | AList (rk, rv) -> Some (strip_scope rk, scope_exn rk, rv, list)
          | AHashIdx h ->
              Some
                ( h.hi_keys,
                  h.hi_scope,
                  h.hi_values,
                  fun rk s rv ->
                    hash_idx'
                      { h with hi_keys = rk; hi_scope = s; hi_values = rv } )
          | AOrderedIdx (rk, rv, m) ->
              Some
                ( strip_scope rk,
                  scope_exn rk,
                  rv,
                  fun rk s rv -> ordered_idx rk s rv m )
          | _ -> None
        in
        let rk_bnd = Set.of_list (module Name) (schema_exn rk) in
        let pushed_key, pushed_val =
          Pred.conjuncts p
          |> List.partition_map ~f:(fun p ->
                 if Tactics_util.is_supported rk_bnd p then `Fst p else `Snd p)
        in
        let inner_key_pred = Pred.conjoin pushed_key in
        let inner_val_pred =
          let pushed_val =
            List.map pushed_val ~f:(Pred.scoped (Set.to_list rk_bnd) scope)
          in
          Pred.conjoin pushed_val
        in
        mk (filter inner_key_pred rk) scope (filter inner_val_pred rv)

  let push_filter =
    (* NOTE: Simplify is necessary to make push-filter safe under fixpoints. *)
    seq' (of_func push_filter ~name:"push-filter") simplify

  let elim_eq_filter_src =
    let src = Logs.Src.create "elim-eq-filter" in
    Logs.Src.set_level src (Some Debug);
    src

  let contains_not p =
    let visitor =
      object (self)
        inherit [_] reduce

        inherit [_] Util.disj_monoid

        method! visit_Unop () (op, p) =
          if op = Not then true else self#visit_pred () p
      end
    in
    visitor#visit_pred () p

  let is_eq_subtree p =
    let visitor =
      object (self)
        inherit [_] reduce

        inherit [_] Util.conj_monoid

        method! visit_Binop () (op, p1, p2) =
          (op = And || op = Or)
          && self#visit_pred () p1 && self#visit_pred () p2
          || op = Eq

        method! visit_Unop () (op, p) = op <> Not && self#visit_pred () p
      end
    in
    visitor#visit_pred () p

  (** Domain computations for predicates containing conjunctions, disjunctions
     and equalities. *)
  module EqDomain = struct
    type domain =
      | And of domain * domain
      | Or of domain * domain
      | Domain of Abslayout.t
    [@@deriving compare]

    type t = domain Map.M(Pred).t

    let intersect d1 d2 =
      Map.merge d1 d2 ~f:(fun ~key:_ v ->
          let ret =
            match v with
            | `Both (d1, d2) ->
                if [%compare.equal: domain] d1 d2 then d1 else And (d1, d2)
            | `Left d | `Right d -> d
          in
          Some ret)

    let union d1 d2 =
      Map.merge d1 d2 ~f:(fun ~key:_ v ->
          let ret =
            match v with
            | `Both (d1, d2) ->
                if [%compare.equal: domain] d1 d2 then d1 else Or (d1, d2)
            | `Left d | `Right d -> d
          in
          Some ret)

    let rec of_pred r =
      let open Or_error.Let_syntax in
      function
      | Binop (And, p1, p2) ->
          let%bind ds1 = of_pred r p1 in
          let%map ds2 = of_pred r p2 in
          intersect ds1 ds2
      | Binop (Or, p1, p2) ->
          let%bind ds1 = of_pred r p1 in
          let%map ds2 = of_pred r p2 in
          union ds1 ds2
      | Binop (Eq, p1, p2) -> (
          match
            (Tactics_util.all_values [ p1 ] r, Tactics_util.all_values [ p2 ] r)
          with
          | _, Ok vs2 when is_candidate_key p1 r && is_candidate_match p2 r ->
              Ok (Map.singleton (module Pred) p1 (Domain vs2))
          | Ok vs1, _ when is_candidate_key p2 r && is_candidate_match p1 r ->
              Ok (Map.singleton (module Pred) p2 (Domain vs1))
          | _, Ok _ | Ok _, _ ->
              Or_error.error "No candidate keys." (p1, p2)
                [%sexp_of: Pred.t * Pred.t]
          | Error e1, Error e2 -> Error (Error.of_list [ e1; e2 ]) )
      | p ->
          Or_error.error "Not part of an equality predicate." p
            [%sexp_of: Pred.t]

    let to_ralgebra d =
      let schema r = List.hd_exn (schema_exn r) in
      let rec extract = function
        | And (d1, d2) ->
            let e1 = extract d1 in
            let e2 = extract d2 in
            let n1 = schema e1 in
            let n2 = schema e2 in
            dedup
              (select [ Name n1 ] (join (Binop (Eq, Name n1, Name n2)) e1 e2))
        | Or (d1, d2) ->
            let e1 = extract d1 in
            let e2 = extract d2 in
            let n1 = schema e1 in
            let n2 = schema e2 in
            let n = Fresh.name Global.fresh "x%d" in
            dedup
              (tuple
                 [
                   select [ Pred.as_pred (Name n1, n) ] e1;
                   select [ Pred.as_pred (Name n2, n) ] e2;
                 ]
                 Concat)
        | Domain d ->
            let n = schema d in
            let n' = Fresh.name Global.fresh "x%d" in
            select [ Pred.as_pred (Name n, n') ] d
      in
      Map.map d ~f:extract
  end

  let elim_eq_filter r =
    let open Option.Let_syntax in
    let%bind p, r = to_filter r in
    let eqs, rest =
      Pred.to_nnf p |> Pred.conjuncts
      |> List.partition_map ~f:(fun p ->
             match EqDomain.of_pred r p with
             | Ok d -> `Fst (p, d)
             | Error e ->
                 Logs.info ~src:elim_eq_filter_src (fun m -> m "%a" Error.pp e);
                 `Snd p)
    in
    let inner, eqs = List.unzip eqs in
    let eqs = List.reduce ~f:EqDomain.intersect eqs in
    let inner = Pred.conjoin inner in
    match eqs with
    | None ->
        Logs.err ~src:elim_eq_filter_src (fun m -> m "Found no equalities.");
        None
    | Some eqs ->
        let eqs = EqDomain.to_ralgebra eqs in
        let scope = Fresh.name Global.fresh "s%d" in
        let key, rels = Map.to_alist eqs |> List.unzip in
        let r_keys = dedup (tuple rels Cross) in
        let inner_filter_pred =
          let ctx =
            Map.map eqs ~f:(fun r ->
                Name (List.hd_exn (schema_exn r) |> Name.scoped scope))
          in
          Pred.subst_tree ctx inner
        in
        let outer_filter_pred = Pred.conjoin rest in
        Some
          (filter outer_filter_pred
             (hash_idx r_keys scope (filter inner_filter_pred r) key))

  let elim_eq_filter =
    seq' (of_func elim_eq_filter ~name:"elim-eq-filter") (try_ filter_const)

  let elim_disjunct ?(max_clauses = 3) r =
    let open Option.Let_syntax in
    let%bind p, r = to_filter r in
    let clauses = Pred.disjuncts p in
    let nclauses = List.length clauses in
    if nclauses > 1 && nclauses <= max_clauses then
      if
        ( try
            Tactics_util.all_disjoint
              (List.map ~f:(Pred.to_static ~params) clauses)
              r
          with _ -> false )
        && List.length clauses > 1
      then Some (tuple (List.map clauses ~f:(fun p -> filter p r)) Concat)
      else None
    else None

  let elim_disjunct = of_func elim_disjunct ~name:"elim-disjunct"

  let to_lower_bound n =
    List.find_map ~f:(function
      | Binop (Eq, Name n', p) when Name.O.(n' = n) -> Some p
      | Binop (Eq, p, Name n') when Name.O.(n' = n) -> Some p
      | Binop (Lt, Name n', p) when Name.O.(n' = n) -> Some p
      | Binop (Le, Name n', p) when Name.O.(n' = n) -> Some p
      | Binop (Gt, p, Name n') when Name.O.(n' = n) -> Some p
      | Binop (Ge, p, Name n') when Name.O.(n' = n) -> Some p
      | Binop (Lt, Binop (Add, Name n', p'), p) when Name.O.(n' = n) ->
          Some (Binop (Sub, p, p'))
      | Binop (Le, Binop (Add, Name n', p'), p) when Name.O.(n' = n) ->
          Some (Binop (Sub, p, p'))
      | Binop (Gt, p, Binop (Add, Name n', p')) when Name.O.(n' = n) ->
          Some (Binop (Sub, p, p'))
      | Binop (Ge, p, Binop (Add, Name n', p')) when Name.O.(n' = n) ->
          Some (Binop (Sub, p, p'))
      | _ -> None)

  let to_upper_bound n =
    List.find_map ~f:(function
      | Binop (Eq, Name n', p) when Name.O.(n' = n) -> Some p
      | Binop (Eq, p, Name n') when Name.O.(n' = n) -> Some p
      | Binop (Lt, p, Name n') when Name.O.(n' = n) -> Some p
      | Binop (Le, p, Name n') when Name.O.(n' = n) -> Some p
      | Binop (Gt, Name n', p) when Name.O.(n' = n) -> Some p
      | Binop (Ge, Name n', p) when Name.O.(n' = n) -> Some p
      | Binop (Lt, p, Binop (Add, Name n', p')) when Name.O.(n' = n) ->
          Some (Binop (Add, p, p'))
      | Binop (Le, p, Binop (Add, Name n', p')) when Name.O.(n' = n) ->
          Some (Binop (Add, p, p'))
      | Binop (Gt, Binop (Add, Name n', p'), p) when Name.O.(n' = n) ->
          Some (Binop (Add, p, p'))
      | Binop (Ge, Binop (Add, Name n', p'), p) when Name.O.(n' = n) ->
          Some (Binop (Add, p, p'))
      | _ -> None)

  let to_range n ps = (to_lower_bound n ps, to_upper_bound n ps)

  let partition _ r =
    let open Option.Let_syntax in
    let part_on r n =
      let visitor =
        object
          inherit [_] reduce as super

          inherit [_] Util.list_monoid

          method! visit_Filter () (p, r) =
            super#visit_Filter () (p, r)
            @ ( Pred.conjuncts p
              |> List.filter ~f:(fun p -> Set.mem (Pred.names p) n) )
        end
      in
      let preds = visitor#visit_t () r in
      let key_range = to_range n preds in
      let%bind fields =
        List.map preds ~f:(fun p -> Set.remove (Pred.names p) n)
        |> List.reduce ~f:Set.union |> Option.map ~f:Set.to_list
      in
      let fields =
        let m = Tactics_util.alias_map r in
        List.map fields ~f:(fun n ->
            (* If n is an alias for a field in a base relation, find the name of
               that field. *)
            match Map.find m n with
            | Some n' -> (n', Some n)
            | None -> (Name n, None))
        |> Map.of_alist_multi (module Pred)
        |> Map.to_alist
      in
      match (fields, key_range) with
      | [ (f, aliases) ], (Some l, Some h) ->
          let key_name = Fresh.name Global.fresh "k%d" in
          let%bind keys =
            match Pred.to_type f with
            | IntT _ | DateT _ ->
                let%map vals = Tactics_util.all_values [ f ] r |> Or_error.ok in
                let vals =
                  let val_name = List.hd_exn (schema_exn vals) in
                  let select_list =
                    Name val_name
                    :: List.filter_map aliases
                         ~f:
                           (Option.map ~f:(fun n ->
                                As_pred (Name val_name, Name.name n)))
                  in
                  select select_list vals
                in
                let scope = Fresh.name Global.fresh "k%d" in
                dep_join
                  (select [ As_pred (Min l, "lo"); As_pred (Max h, "hi") ] vals)
                  scope
                  (select
                     [ As_pred (Name (Name.create "range"), key_name) ]
                     (range
                        (Name (Name.create ~scope "lo"))
                        (Name (Name.create ~scope "hi"))))
            | StringT _ ->
                let%map keys = Tactics_util.all_values [ f ] r |> Or_error.ok in
                select
                  [ As_pred (Name (List.hd_exn (schema_exn keys)), key_name) ]
                  keys
            | _ -> None
          in
          let scope = Fresh.name Global.fresh "s%d" in
          let r' =
            subst
              (Map.singleton
                 (module Name)
                 n
                 (Name (Name.scoped scope (Name.create key_name))))
              r
          in
          if Set.mem (names r') n then None
          else Some (hash_idx keys scope r' [ Name n ])
      | fs, _ ->
          Logs.debug (fun m ->
              m "Partition: Found too many fields. %a" (Fmt.list Pred.pp)
                (List.map ~f:Tuple.T2.get1 fs));
          None
    in
    let r = Resolve.resolve ~params r in
    Set.to_sequence params |> Seq.filter_map ~f:(part_on r)

  let partition = Branching.global partition ~name:"partition"

  let elim_subquery _ r =
    let open Option.Let_syntax in
    let%bind p, r = to_filter r in
    let schema_names = schema_exn r |> Set.of_list (module Name) in
    let visitor =
      object
        inherit [_] mapreduce

        inherit [_] Util.list_monoid

        method! visit_Exists () r =
          if Set.inter schema_names (names r) |> Set.is_empty then
            let qname = Fresh.name Global.fresh "q%d" in
            ( Name (Name.create qname),
              [ select [ As_pred (Binop (Gt, Count, Int 0), qname) ] r ] )
          else (Exists r, [])

        method! visit_First () r =
          let n = schema_exn r |> List.hd_exn in
          if Set.inter schema_names (names r) |> Set.is_empty then
            let qname = Fresh.name Global.fresh "q%d" in
            ( Name (Name.create qname),
              [ select [ As_pred (Min (Name n), qname) ] r ] )
          else (Exists r, [])
      end
    in
    let p, subqueries = visitor#visit_pred () p in
    if List.length subqueries > 0 then
      let scope = Fresh.name Global.fresh "s%d" in
      let sq_tuple = tuple subqueries Cross in
      Some
        (dep_join sq_tuple scope
           (filter (Pred.scoped (schema_exn sq_tuple) scope p) r))
    else None

  (* let precompute_filter n =
   *   let exception Failed of Error.t in
   *   let run_exn r =
   *     M.annotate_schema r ;
   *     match r.node with
   *     | Filter (p, r') ->
   *         let schema = Meta.(find_exn r' schema) in
   *         let free_vars =
   *           Set.diff (pred_free p) (Set.of_list (module Name) schema)
   *           |> Set.to_list
   *         in
   *         let free_var =
   *           match free_vars with
   *           | [v] -> v
   *           | _ ->
   *               let err =
   *                 Error.of_string
   *                   "Unexpected number of free variables in predicate."
   *               in
   *               raise (Failed err)
   *         in
   *         let witness_name = Fresh.name fresh "wit%d_" in
   *         let witnesses =
   *           List.mapi values ~f:(fun i v ->
   *               As_pred
   *                 ( subst_pred (Map.singleton (module Name) free_var v) p
   *                 , sprintf "%s_%d" witness_name i ) )
   *         in
   *         let filter_pred =
   *           List.foldi values ~init:p ~f:(fun i else_ v ->
   *               If
   *                 ( Binop (Eq, Name free_var, v)
   *                 , Name (Name.create (sprintf "%s_%d" witness_name i))
   *                 , else_ ) )
   *         in
   *         let select_list = witnesses @ List.map schema ~f:(fun n -> Name n) in
   *         Some (filter filter_pred (select select_list r'))
   *     | _ -> None
   *   in
   *   let f r = try run_exn r with Failed _ -> None in
   *   of_func f ~name:"precompute-filter" *)
end
