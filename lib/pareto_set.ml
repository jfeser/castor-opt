open! Core

let empty = []

let singleton c v = [ (c, v) ]

let dominates x y =
  assert (Array.length x = Array.length y);
  let n = Array.length x in
  let rec loop i le lt =
    if i = n then le && lt
    else loop (i + 1) Float.(le && x.(i) <= y.(i)) Float.(lt || x.(i) < y.(i))
  in
  loop 0 true false

let rec add s c v =
  match s with
  | [] -> [ (c, v) ]
  | (c', v') :: s' ->
      if Array.equal Float.( = ) c c' || dominates c' c then s
      else if dominates c c' then add s' c v
      else (c', v') :: add s' c v

let min_elt f s =
  List.map s ~f:(fun (c, x) -> (f c, x))
  |> List.min_elt ~compare:(fun (c1, _) (c2, _) -> Float.compare c1 c2)
  |> Option.map ~f:(fun (_, x) -> x)

let of_list l = List.fold_left l ~init:[] ~f:(fun s (c, v) -> add s c v)

let union_all ss = List.concat ss |> of_list
