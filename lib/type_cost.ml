open Ast
open Abslayout_load
open Type
module I = Abs_int

include (val Log.make ~level:(Some Warning) "castor-opt.type-cost")

let timeout = ref None

let kind = ref `Max

let param =
  let open Command in
  let kind_type =
    let kinds = [ ("min", `Min); ("max", `Max); ("avg", `Avg) ] in
    Arg_type.create (fun s ->
        List.find_map_exn kinds ~f:(fun (s', k) ->
            if String.(s = s') then Some k else None))
  in
  let open Command.Let_syntax in
  [%map_open
    let () = param
    and timeout' =
      flag "cost-timeout" (optional float)
        ~doc:"SEC time to run cost estimation"
    and kind' =
      flag "cost-agg"
        (optional_with_default `Max kind_type)
        "AGG how to aggregate costs"
    in
    timeout := timeout';
    kind := kind']

module Config = struct
  module type S = sig
    val params : Set.M(Name).t

    val cost_conn : Db.t
  end
end

module Make (Config : Config.S) = struct
  open Config

  let rec read = function
    | StringT { nchars = Top; _ } -> (* TODO: Fix this... *) I.Interval (5, 50)
    | (NullT | EmptyT | IntT _ | DateT _ | FixedT _ | BoolT _ | StringT _) as t
      ->
        len t
    | ListT (elem_t, m) -> I.(read elem_t * m.count)
    | FuncT ([ t ], _) -> read t
    | FuncT ([ t1; t2 ], _) -> I.(read t1 * read t2)
    | FuncT _ -> failwith "Unexpected function."
    | TupleT (elem_ts, { kind = `Concat }) ->
        List.sum (module I) elem_ts ~f:read
    | TupleT (elem_ts, { kind = `Cross }) ->
        let rec cost = function
          | [] -> I.zero
          | [ x ] -> read x
          | x :: xs -> I.(read x + (count x * cost xs))
        in
        cost elem_ts
    | HashIdxT (_, vt, _) -> I.(join zero (read vt))
    | OrderedIdxT (kt, vt, { key_count }) ->
        I.(join zero (read kt * key_count) + join zero (read vt))

  let cost ?(kind = !kind) =
    Memo.general
      ~hashable:(Hashtbl.Hashable.of_key (module Ast))
      (fun r ->
        info (fun m -> m "Computing cost of:@, %a." Abslayout.pp r);
        let out =
          let open Result.Let_syntax in
          let%bind layout = load_layout ~params cost_conn r in
          let%bind type_ =
            strip_meta layout |> Parallel.type_of ?timeout:!timeout cost_conn
          in
          let c = read type_ in
          match kind with
          | `Min -> I.inf c
          | `Max -> I.sup c
          | `Avg ->
              let%bind l = I.inf c in
              let%map h = I.sup c in
              l + ((h - l) / 2)
        in
        match out with
        | Ok x ->
            let x = Float.of_int x in
            info (fun m -> m "Found cost %f." x);
            x
        | Error e ->
            warn (fun m ->
                m "Computing cost failed: %a"
                  (Resolve.pp_err @@ Parallel.pp_err @@ Fmt.nop)
                  e);
            Float.max_value)
end
