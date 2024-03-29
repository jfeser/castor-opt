open Ast
module A = Abslayout

module Config = struct
  module type S = sig
    include Ops.Config.S

    include Tactics_util.Config.S

    val params : Set.M(Name).t
  end
end

module Make (Config : Config.S) = struct
  open Ops.Make (Config)

  module Tactics_util = Tactics_util.Make (Config)

  let key_is_supported r key =
    let s = Set.of_list (module Name) (Schema.schema r) in
    List.for_all key ~f:(fun (p, _) ->
        Tactics_util.is_supported r.meta#stage s p)

  module C = (val Constructors.Annot.with_strip_meta (fun () -> object end))

  let push_orderby_depjoin key mk lhs scope rhs meta =
    let open Option.Let_syntax in
    let used_names =
      let schema_rhs = Schema.schema rhs |> Set.of_list (module Name) in
      List.map key ~f:(fun (p, _) -> Free.pred_free p)
      |> Set.union_list (module Name)
      |> Set.inter schema_rhs |> Set.to_list
    in
    let eqs =
      let unscope n =
        match Name.rel n with
        | Some s when String.(s = scope) -> Name.unscoped n
        | _ -> n
      in
      Set.map
        (module Equiv.Eq)
        meta#meta#eq
        ~f:(fun (n, n') -> (unscope n, unscope n'))
    in
    let%map ctx =
      Join_elim.translate eqs ~from:used_names ~to_:(Schema.schema lhs)
    in
    let ctx =
      List.map ctx ~f:(fun (n, n') -> (n, Name n'))
      |> Map.of_alist_exn (module Name)
    in
    let key = List.map key ~f:(fun (p, o) -> (Pred.subst ctx p, o)) in
    mk (C.order_by key lhs) scope rhs

  let push_orderby r =
    let open C in
    let orderby_cross_tuple key rs =
      match rs with
      | r :: rs ->
          if key_is_supported r key then
            Some (tuple (order_by key r :: List.map ~f:strip_meta rs) Cross)
          else None
      | _ -> None
    in
    match r.node with
    | OrderBy { key; rel = { node = Select (ps, r); _ } } ->
        if key_is_supported r key then Some (select ps (order_by key r))
        else None
    | OrderBy { key; rel = { node = Filter (ps, r); _ } } ->
        Some (filter ps (order_by key r))
    | OrderBy { key; rel = { node = AHashIdx h; _ } } ->
        Some
          (hash_idx ?key_layout:h.hi_key_layout h.hi_keys h.hi_scope
             (order_by key h.hi_values) h.hi_lookup)
    | OrderBy { key; rel = { node = ATuple (rs, Cross); _ } } ->
        orderby_cross_tuple key rs
    | OrderBy { key; rel = { node = DepJoin d; meta } } ->
        push_orderby_depjoin key dep_join d.d_lhs d.d_alias d.d_rhs meta
    | OrderBy { key; rel = { node = AList l; meta } } ->
        push_orderby_depjoin key list l.l_keys l.l_scope l.l_values meta
    | _ -> None

  let push_orderby =
    of_func_pre push_orderby ~name:"push-orderby" ~pre:(fun r ->
        r |> Equiv.annotate |> Resolve.resolve_exn ~params:Config.params)
end
