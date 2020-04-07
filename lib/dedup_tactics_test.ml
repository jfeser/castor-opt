open Abslayout
open Abslayout_load
open Castor_test.Test_util

module C = struct
  let params = Set.empty (module Name)

  let conn = Lazy.force test_db_conn

  let cost_conn = Lazy.force test_db_conn
end

open Dedup_tactics.Make (C)

open Ops.Make (C)

let%expect_test "no-push-list" =
  let r =
    load_string_exn (Lazy.force tpch_conn)
      {|
    dedup(alist(atuple([ascalar(0 as x), ascalar(0 as x), ascalar(1 as x)], concat) as k,
    ascalar(1 as y)))
|}
  in
  apply push_dedup Path.root r |> Option.iter ~f:(Fmt.pr "%a" pp)

let%expect_test "push-list" =
  let r =
    load_string_exn (Lazy.force tpch_conn)
      {|
    dedup(alist(atuple([ascalar(0 as x), ascalar(0 as x), ascalar(1 as x)], concat) as k,
    atuple([ascalar(k.x), ascalar(1 as y)], cross)))
|}
  in
  apply push_dedup Path.root r |> Option.iter ~f:(Fmt.pr "%a" pp);
  [%expect
    {|
    alist(dedup(
            atuple([ascalar(0 as x), ascalar(0 as x), ascalar(1 as x)], concat)) as k,
      dedup(atuple([ascalar(k.x), ascalar(1 as y)], cross))) |}]
