open! Core
open Castor
open Graph

module Vertex = struct
  include Abslayout

  let equal = [%compare.equal: t]
end

module Edge = struct
  include Pred

  let default = Abslayout.Bool true
end

module G = Persistent.Graph.ConcreteLabeled (Vertex) (Edge)
include G
include Oper.P (G)
module Dfs = Traverse.Dfs (G)
include Oper.Choose (G)

let to_string g = sprintf "graph (|V|=%d) (|E|=%d)" (nb_vertex g) (nb_edges g)

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
        (lhs, rhs))
      g (g, g)
  in
  let es =
    fold_edges_e
      (fun ((v1, _, v2) as e) es ->
        if
          (Set.mem vs v1 && not (Set.mem vs v2))
          || ((not (Set.mem vs v1)) && Set.mem vs v2)
        then e :: es
        else es)
      g []
  in
  (g1, g2, es)

let is_connected g =
  let n = nb_vertex g in
  let n = Dfs.fold_component (fun _ i -> i - 1) n g (choose_vertex g) in
  n = 0
