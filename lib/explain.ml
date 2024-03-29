open Yojson.Basic
open Postgresql

type t = { nrows : int; cost : float }

let explain (conn : Db.t) query =
  let open Result.Let_syntax in
  let r : result =
    (Db.conn conn)#exec (sprintf "explain (format json) %s" query)
  in
  let%bind json_str =
    match r#status with
    | Single_tuple | Tuples_ok -> Ok (r#getvalue 0 0)
    | _ ->
        let status = result_status r#status in
        Result.fail
          Error.(
            create "Postgres error." (status, r#error, query)
              [%sexp_of: string * string * string])
  in
  let json = from_string json_str in
  try
    let plan = Util.to_list json |> List.hd_exn |> Util.member "Plan" in
    let nrows = Util.member "Plan Rows" plan |> Util.to_int in
    let cost = Util.member "Total Cost" plan |> Util.to_number in
    Ok { nrows; cost }
  with Util.Type_error _ as e ->
    Result.fail Error.(of_exn e |> tag ~tag:json_str)
