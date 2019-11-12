open! Core
open! Castor
module A = Abslayout
module G = Join_graph

module T = struct
  type t = { graph : G.t; filters : Set.M(Pred).t Map.M(G.Vertex).t }
  [@@deriving compare, sexp_of]

  let t_of_sexp _ = failwith "unimplemented"
end

include T
module C = Comparable.Make (T)

module O : Comparable.Infix with type t := t = C

let to_string { graph; _ } = G.to_string graph

let empty = { graph = G.empty; filters = Map.empty (module G.Vertex) }

let union s1 s2 =
  let merger ~key:_ = function
    | `Left x | `Right x -> Some x
    | `Both (x, y) -> Some (Set.union x y)
  in
  {
    graph = G.union s1.graph s2.graph;
    filters = Map.merge ~f:merger s1.filters s2.filters;
  }

let length { graph; _ } = G.nb_vertex graph

let choose { graph; _ } = G.choose_vertex graph

let contract join g =
  let open G in
  (* if the edge is to be removed (property = true):
   * make a union of the two union-sets of start and end node;
   * put this set in the map for all nodes in this set *)
  let f edge m =
    let s_src, j_src = Map.find_exn m (E.src edge) in
    let s_dst, j_dst = Map.find_exn m (E.dst edge) in
    let s = Set.union s_src s_dst in
    let j = join ~label:(G.E.label edge) j_src j_dst in
    Set.fold ~f:(fun m vertex -> Map.set m ~key:vertex ~data:(s, j)) s ~init:m
  in
  (* initialize map with singleton-sets for every node (of itself) *)
  let m =
    G.fold_vertex
      (fun vertex m ->
        Map.set m ~key:vertex
          ~data:(Set.singleton (module Vertex) vertex, vertex))
      g
      (Map.empty (module Vertex))
  in
  G.fold_edges_e f g m |> Map.data |> List.hd_exn |> fun (_, j) -> j

let to_ralgebra { graph; _ } =
  if G.nb_vertex graph = 1 then G.choose_vertex graph
  else contract (fun ~label:p j1 j2 -> A.join p j1 j2) graph

(** Collect the leaves of the join tree rooted at r. *)
let rec to_leaves r =
  let open A in
  match r.node with
  | Join { r1; r2; _ } -> Set.union (to_leaves r1) (to_leaves r2)
  | _ -> Set.singleton (module A) r

let source_relation leaves n =
  List.find_map leaves ~f:(fun (r, s) -> if Set.mem s n then Some r else None)
  |> Result.of_option
       ~error:
         Error.(
           create "No source found for name."
             (n, List.map leaves ~f:(fun (_, ns) -> ns))
             [%sexp_of: Name.t * Set.M(Name).t list])

(** Convert a join tree to a join graph. *)
let rec to_graph leaves r =
  match r.A.node with
  | Join { r1; r2; pred = p } ->
      let s = union (to_graph leaves r1) (to_graph leaves r2) in
      (* Collect the set of relations that this join depends on. *)
      List.fold_left (Pred.conjuncts p) ~init:s ~f:(fun s p ->
          let pred_rels =
            List.map (Pred.names p |> Set.to_list) ~f:(source_relation leaves)
            |> Or_error.all
          in
          match pred_rels with
          | Ok [] ->
              Logs.warn (fun m ->
                  m "Join-opt: Unhandled predicate %a. Constant predicate."
                    A.pp_pred p);
              s
          | Ok [ r ] ->
              {
                s with
                filters =
                  Map.update s.filters r ~f:(function
                    | Some fs -> Set.add fs p
                    | None -> Set.singleton (module Pred) p);
              }
          | Ok [ r1; r2 ] ->
              { s with graph = G.add_or_update_edge s.graph (r1, p, r2) }
          | Ok _ ->
              Logs.warn (fun m ->
                  m "Join-opt: Unhandled predicate %a. Too many relations."
                    A.pp_pred p);
              s
          | Error e ->
              Logs.warn (fun m ->
                  m "Join opt: Unhandled predicate %a. %a" A.pp_pred p Error.pp
                    e);
              s)
  | _ -> empty

let of_abslayout r =
  Logs.debug (fun m -> m "Join-opt: Planning join for %a." A.pp r);
  let leaves =
    to_leaves r |> Set.to_list
    |> List.map ~f:(fun r ->
           let s = A.schema_exn r |> Set.of_list (module Name) in
           (r, s))
  in
  to_graph leaves r

let partition_fold ~init ~f s =
  let vertices = G.vertices s.graph |> Array.of_list in
  let n = Array.length vertices in
  let rec loop acc k =
    if k >= n then acc
    else
      let acc =
        Combinat.Combination.fold (k, n) ~init:acc ~f:(fun acc vs ->
            let g1, g2, es =
              G.partition s.graph
                ( List.init k ~f:(fun i -> vertices.(vs.{i}))
                |> Set.of_list (module G.Vertex) )
            in
            if G.is_connected g1 && G.is_connected g2 then
              let s1 = { s with graph = g1 } in
              let s2 = { s with graph = g2 } in
              f acc (s1, s2, es)
            else acc)
      in
      loop acc (k + 1)
  in
  loop init 1
