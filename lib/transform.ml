open Collections
open Ast
module R = Resolve
module V = Visitors

module Config = struct
  module type S = sig
    val conn : Db.t

    val cost_conn : Db.t

    val params : Set.M(Name).t

    val cost_timeout : float option

    val random : Mcmc.Random_choice.t
  end
end

module Make (Config : Config.S) = struct
  open Config
  module O = Ops.Make (Config)
  open O
  module Filter_tactics = Filter_tactics.Make (Config)
  module Simple_tactics = Simple_tactics.Make (Config)
  module Join_opt = Join_opt.Make (Config)
  module Simplify_tactic = Simplify_tactic.Make (Config)
  module Select_tactics = Select_tactics.Make (Config)
  module Groupby_tactics = Groupby_tactics.Make (Config)
  module Join_elim_tactics = Join_elim_tactics.Make (Config)
  module Tactics_util = Tactics_util.Make (Config)
  module Dedup_tactics = Dedup_tactics.Make (Config)
  module Orderby_tactics = Orderby_tactics.Make (Config)
  module Cost = Type_cost.Make (Config)

  let try_random tf =
    global
      (fun p r ->
        if Mcmc.Random_choice.rand random tf.name (Path.get_exn p r) then
          apply tf p r
        else Some r)
      "try-random"

  let try_random_branch tf =
    Branching.global ~name:"try-random" (fun p r ->
        if Mcmc.Random_choice.rand random (Branching.name tf) (Path.get_exn p r)
        then Branching.apply tf p r
        else Seq.singleton r)

  let is_serializable r p =
    Is_serializable.is_serializeable ~params ~path:p r |> Result.is_ok

  let is_spine_serializable r p =
    Is_serializable.is_spine_serializeable ~params ~path:p r |> Result.is_ok

  let has_params r p = Path.get_exn p r |> Free.free |> overlaps params

  let has_free r p = not (Set.is_empty (Free.free (Path.get_exn p r)))

  let push_all_runtime_filters =
    for_all Filter_tactics.push_filter Path.(all >>? is_run_time >>? is_filter)

  let push_static_filters =
    for_all Filter_tactics.push_filter
      Path.(all >>? is_run_time >>? is_filter >>? Infix.not is_param_filter)

  let hoist_all_filters =
    for_all Filter_tactics.hoist_filter Path.(all >>? is_filter >> O.parent)

  let elim_param_filter tf test =
    (* Eliminate comparison filters. *)
    fix @@ traced
    @@ seq_many
         [
           (* Hoist parameterized filters as far up as possible. *)
           for_all Filter_tactics.hoist_filter
             (Path.all >>? is_param_filter >> parent);
           Branching.(
             seq_many
               [
                 unroll_fix @@ O.traced
                 @@ O.at_ Filter_tactics.push_filter
                      Path.(all >>? test >>? is_run_time >>| shallowest);
                 (* Eliminate a comparison filter. *)
                 choose
                   (for_all (try_random_branch tf)
                      Path.(all >>? test >>? is_run_time))
                   id;
                 lift
                   (O.seq_many
                      [
                        push_all_runtime_filters;
                        O.for_all Simple_tactics.row_store
                          Path.(all >>? is_run_time >>? is_relation);
                        push_all_runtime_filters;
                        fix Simplify_tactic.project;
                        Simplify_tactic.simplify;
                      ]);
               ]
             |> lower (min Cost.cost));
         ]

  let try_partition tf =
    traced ~name:"try-partition"
    @@ Branching.(
         seq_many
           [
             choose id (try_random_branch @@ traced Filter_tactics.partition);
             lift tf;
           ]
         |> lower (min Cost.cost))

  let try_ tf rest =
    Branching.(seq (choose (lift tf) id) (lift rest) |> lower (min Cost.cost))

  let try_many tfs rest =
    Branching.(
      seq (choose_many (List.map ~f:lift tfs)) (lift rest)
      |> lower (min Cost.cost))

  let is_serializable' r =
    let bad_runtime_op =
      Path.(
        all >>? is_run_time
        >>? Infix.(
              is_join || is_groupby || is_orderby || is_dedup || is_relation))
        r
      |> Seq.is_empty |> not
    in
    let mis_bound_params =
      Path.(all >>? is_compile_time) r
      |> Seq.for_all ~f:(fun p ->
             not (overlaps (Free.free (Path.get_exn p r)) params))
      |> not
    in
    if bad_runtime_op then Error (Error.of_string "Bad runtime operation.")
    else if mis_bound_params then
      Error (Error.of_string "Parameters referenced at compile time.")
    else Ok ()

  let is_serializable'' r = Result.is_ok @@ is_serializable' r

  let _elim_subqueries =
    seq_many
      [
        Filter_tactics.elim_all_correlated_subqueries;
        Simplify_tactic.unnest_and_simplify;
      ]

  let cse =
    traced ~name:"cse"
    @@ seq_many'
         [
           for_all Join_elim_tactics.push_join_filter Path.(all >>? is_join);
           for_all' Filter_tactics.cse_filter Path.(all >>? is_filter);
         ]

  let opt =
    let open Infix in
    seq_many
      [
        seq_many
          [
            (* Simplify predicates. *)
            traced ~name:"simplify-preds"
            @@ for_all Filter_tactics.simplify_filter Path.all;
            (* CSE *)
            seq_many'
              [
                cse;
                for_all Select_tactics.push_select Path.(all >>? is_select);
                for_all Simple_tactics.row_store
                  Path.(
                    all >>? is_run_time >>? not has_params
                    >>? not is_serializable
                    >>? not (contains is_collection));
              ];
            (* Eliminate groupby operators. *)
            traced ~name:"elim-groupby"
            @@ fix
            @@ seq_many
                 [
                   first Groupby_tactics.elim_groupby Path.(all >>? is_groupby);
                   fix push_static_filters;
                   for_all Join_elim_tactics.push_join_filter
                     Path.(all >>? is_join);
                 ];
            (* Hoist parameterized filters as far up as possible. *)
            traced ~name:"hoist-param-filters"
            @@ try_random
            @@ seq_many
                 [
                   for_all Join_elim_tactics.hoist_join_param_filter
                     Path.(all >>? is_join);
                   for_all Filter_tactics.hoist_filter
                     Path.(all >>? is_param_filter >> O.parent);
                 ];
            try_random
            @@ traced ~name:"elim-simple-filter"
            @@ at_ Filter_tactics.elim_simple_filter
                 Path.(all >>? is_expensive_filter >>| shallowest);
            (* Eliminate unparameterized join nests. Try using join optimization and
               using a simple row store. *)
            traced ~name:"elim-join-nests"
            @@ try_many
                 [
                   traced ~name:"elim-join-nests-opt"
                   @@ try_random
                   @@ for_all Join_opt.transform
                        Path.(all >>? is_join >>? is_run_time);
                   traced ~name:"elim-join-nests-flat"
                   @@ try_random
                   @@ at_ Simple_tactics.row_store
                        Path.(
                          all >>? is_join >>? is_run_time >>? not has_free
                          >>| shallowest);
                   id;
                 ]
                 (seq_many
                    [
                      try_random @@ traced @@ Filter_tactics.elim_subquery;
                      try_random @@ push_all_runtime_filters;
                      Simplify_tactic.project;
                      traced ~name:"elim-join-filter"
                      @@ at_ Join_elim_tactics.elim_join_filter
                           Path.(all >>? is_join >>| shallowest);
                      try_
                        (traced ~name:"elim-disjunct"
                           (seq_many
                              [
                                hoist_all_filters;
                                first Filter_tactics.elim_disjunct
                                  Path.(all >>? is_filter >>? is_run_time);
                                push_all_runtime_filters;
                              ]))
                        (seq_many
                           [
                             (* Push constant filters *)
                             traced ~name:"push-constant-filters"
                             @@ for_all Filter_tactics.push_filter
                                  Castor.Path.(all >>? is_const_filter);
                             (* Push orderby operators into compile time position if possible. *)
                             traced ~name:"push-orderby"
                             @@ for_all Orderby_tactics.push_orderby
                                  Path.(all >>? is_orderby >>? is_run_time);
                             (* Eliminate comparison filters. *)
                             traced ~name:"elim-cmp-filters"
                             @@ elim_param_filter Filter_tactics.elim_cmp_filter
                                  is_param_cmp_filter;
                             (* Eliminate equality filters. *)
                             traced ~name:"elim-eq-filters"
                             @@ elim_param_filter
                                  (Branching.lift Filter_tactics.elim_eq_filter)
                                  is_param_filter;
                             traced ~name:"push-all-unparam-filters"
                             @@ push_all_runtime_filters;
                             (* Eliminate all unparameterized relations. *)
                             traced ~name:"elim-unparam-relations"
                             @@ fix
                             @@ seq_many
                                  [
                                    at_ Simple_tactics.row_store
                                      Path.(
                                        all >>? is_run_time >>? not has_params
                                        >>? not is_serializable
                                        >>? not (contains is_collection)
                                        >>| shallowest);
                                    push_all_runtime_filters;
                                  ];
                             traced ~name:"push-all-unparam-filters"
                             @@ push_all_runtime_filters;
                             (* Push selections above collections. *)
                             traced ~name:"push-select-above-collection"
                             @@ for_all Select_tactics.push_select
                                  Path.(
                                    all >>? is_select >>? is_run_time
                                    >>? above is_collection);
                             (* Push orderby operators into compile time position if possible. *)
                             traced ~name:"push-orderby-into-ctime"
                             @@ for_all Orderby_tactics.push_orderby
                                  Path.(all >>? is_orderby >>? is_run_time)
                             (* Last-ditch tactic to eliminate orderby. *);
                             traced ~name:"final-orderby-elim"
                             @@ for_all Simple_tactics.row_store
                                  Path.(all >>? is_orderby >>? is_run_time);
                             (* Try throwing away structure if it reduces overall cost. *)
                             ( traced ~name:"drop-structure"
                             @@ Branching.(
                                  seq_many
                                    [
                                      choose id
                                        (seq_many
                                           [
                                             for_all
                                               (lift Simple_tactics.row_store)
                                               Path.(
                                                 all >>? is_run_time
                                                 >>? not has_params
                                                 >>? not is_scalar);
                                             lift push_all_runtime_filters;
                                           ]);
                                      filter is_spine_serializable;
                                    ]
                                  |> lower (min Cost.cost)) );
                             (* Cleanup*)
                             traced ~name:"cleanup" @@ fix
                             @@ seq_many
                                  [
                                    for_all Select_tactics.push_simple_select
                                      Path.(all >>? is_select);
                                    for_all Dedup_tactics.push_dedup
                                      Path.(all >>? is_dedup);
                                    for_all Dedup_tactics.elim_dedup
                                      Path.(all >>? is_dedup);
                                  ];
                             traced ~name:"project"
                             @@ fix Simplify_tactic.project;
                             traced ~name:"prf" @@ push_all_runtime_filters;
                             traced ~name:"simp" @@ Simplify_tactic.simplify;
                             traced @@ filter is_serializable'';
                           ]);
                    ]);
          ];
      ]

  let is_serializable = is_serializable'
end

exception Optimize_failure of Ast.t

let rec optimize_exn (module C : Config.S) r =
  (* Optimize outer query. *)
  let module T = Make (C) in
  let module O = Ops.Make (C) in
  let r =
    match O.apply T.(try_partition opt) Path.root r with
    | Some r -> r
    | None -> raise (Optimize_failure r)
  in
  optimize_subqueries (module C : Config.S) r

(* Recursively optimize subqueries. *)
and optimize_subqueries (module C : Config.S) r =
  let visitor =
    object (self : 'a)
      inherit [_] V.map

      method visit_subquery r =
        let module C = struct
          include C

          let params = Set.union params (Free.free r)
        end in
        optimize_exn (module C) r

      method! visit_Exists () r = Exists (self#visit_subquery r)

      method! visit_First () r = First (self#visit_subquery r)

      method! visit_AList () l =
        AList { l with l_values = self#visit_t () l.l_values }

      method! visit_AOrderedIdx () o =
        AOrderedIdx { o with oi_values = self#visit_t () o.oi_values }

      method! visit_AHashIdx () h =
        AHashIdx { h with hi_values = self#visit_t () h.hi_values }

      method! visit_AScalar () v = AScalar v
    end
  in
  visitor#visit_t () r

let optimize (module C : Config.S) r =
  try Either.First (optimize_exn (module C) r)
  with Optimize_failure r' -> Second r'
