open Ast
open Collections
module A = Abslayout

module Config = struct
  module type S = sig
    val params : Set.M(Name).t

    include Ops.Config.S

    include Select_tactics.Config.S

    include Dedup_tactics.Config.S
  end
end

module Make (Config : Config.S) = struct
  open Config

  open Ops.Make (Config)

  module Select_tactics = Select_tactics.Make (Config)
  module Dedup_tactics = Dedup_tactics.Make (Config)

  let row_store r =
    (* Relation has no free variables that are bound at runtime. *)
    if Is_serializable.is_static ~params r then
      let scope = Fresh.name Global.fresh "s%d" in
      let scalars =
        Schema.schema r |> Schema.scoped scope
        |> List.map ~f:(fun n -> A.scalar (Name n))
      in
      Some (A.list (strip_meta r) scope (A.tuple scalars Cross))
    else None

  let row_store =
    of_func_pre row_store ~pre:Is_serializable.annotate_stage
      ~name:"to-row-store"

  let project r = Some (r |> Resolve.resolve_exn ~params |> Project.project_once)

  let project = of_func project ~name:"project"

  let cleanup =
    fix
    @@ seq_many
         [
           for_all Select_tactics.push_simple_select Path.(all >>? is_select);
           for_all Dedup_tactics.push_dedup Path.(all >>? is_dedup);
           for_all Dedup_tactics.elim_dedup Path.(all >>? is_dedup);
           fix project;
         ]
end
