open Abslayout
open Abslayout_load
open Castor_test.Test_util

module C = struct
  let conn = Lazy.force test_db_conn

  let cost_conn = Lazy.force test_db_conn

  let params = Set.empty (module Name)
end

open Simple_tactics.Make (C)

open Ops.Make (C)

let%expect_test "row-store-comptime" =
  let r = load_string_exn C.conn "alist(r as r1, filter(r1.f = f, r))" in
  Option.iter
    (apply (at_ row_store Path.(all >>? is_filter >>| shallowest)) Path.root r)
    ~f:(Format.printf "%a\n" pp);
  [%expect
    {|
    alist(r as r1,
      alist(filter((r1.f = f), r) as s0,
        atuple([ascalar(s0.f), ascalar(s0.g)], cross))) |}]

let%expect_test "row-store-runtime" =
  let r = load_string_exn C.conn "depjoin(r as r1, filter(r1.f = f, r))" in
  Option.iter
    (apply (at_ row_store Path.(all >>? is_filter >>| shallowest)) Path.root r)
    ~f:(Format.printf "%a\n" pp);
  [%expect {| |}]

let%expect_test "cleanup" =
  let r =
    load_string_exn (Lazy.force tpch_conn)
      {|
select([p_brand, p_type, p_size, supplier_cnt],
  alist(dedup(
          select([p_brand, p_type, p_size],
            dedup(
              select([p_type, p_brand, p_size, ps_suppkey],
                join(((p_partkey = ps_partkey) && true),
                  part,
                  filter(not(exists(filter(((ps_suppkey = s_suppkey) &&
                                           ((strpos(s_comment, "Customer") >= 1) &&
                                           (strpos(s_comment, "Complaints") >= 1))),
                                      supplier))),
                    partsupp)))))) as k0,
    select([p_brand, p_type, p_size, count() as supplier_cnt],
      dedup(
        select([p_type, p_brand, p_size, ps_suppkey],
          alist(join(((not(exists(filter(((ps_suppkey = s_suppkey) &&
                                         ((strpos(s_comment, "Customer") >= 1) &&
                                         (strpos(s_comment, "Complaints") >= 1))),
                                    supplier))) &&
                      ((p_brand = k0.p_brand) && ((p_type = k0.p_type) && (p_size = k0.p_size)))) &&
                     (p_partkey = ps_partkey)),
                  part,
                  partsupp) as s5,
            filter((not((p_brand = "")) &&
                   (not((strpos(p_type, "") = 1)) &&
                   ((p_size = 0) ||
                   ((p_size = 0) ||
                   ((p_size = 0) ||
                   ((p_size = 0) ||
                   ((p_size = 0) || ((p_size = 0) || ((p_size = 0) || (p_size = 0)))))))))),
              atuple([ascalar(s5.p_partkey), ascalar(s5.p_name), ascalar(s5.p_mfgr), 
                      ascalar(s5.p_brand), ascalar(s5.p_type), ascalar(s5.p_size), 
                      ascalar(s5.p_container), ascalar(s5.p_retailprice), 
                      ascalar(s5.p_comment), ascalar(s5.ps_partkey), 
                      ascalar(s5.ps_suppkey), ascalar(s5.ps_availqty), 
                      ascalar(s5.ps_supplycost), ascalar(s5.ps_comment)],
                cross))))))))
|}
  in
  apply cleanup Path.root r |> Option.iter ~f:(Fmt.pr "%a" pp);
  [%expect {|
    alist(dedup(
            select([p_brand, p_type, p_size],
              dedup(
                select([p_type, p_brand, p_size],
                  join(((p_partkey = ps_partkey) && true),
                    part,
                    filter(not(exists(filter(((ps_suppkey = s_suppkey) &&
                                             ((strpos(s_comment, "Customer") >=
                                              1) &&
                                             (strpos(s_comment, "Complaints") >=
                                             1))),
                                        supplier))),
                      partsupp)))))) as k0,
      select([p_brand, p_type, p_size, supplier_cnt],
        select([p_brand, p_type, p_size, count() as supplier_cnt],
          alist(select([p_brand, p_type, p_size],
                  dedup(
                    select([p_brand, p_type, p_size, ps_suppkey],
                      select([p_brand, p_type, p_size, ps_suppkey],
                        join(((not(exists(filter(((ps_suppkey = s_suppkey) &&
                                                 ((strpos(s_comment, "Customer")
                                                  >= 1) &&
                                                 (strpos(s_comment, "Complaints")
                                                 >= 1))),
                                            supplier))) &&
                              ((p_brand = k0.p_brand) &&
                              ((p_type = k0.p_type) && (p_size = k0.p_size)))) &&
                             (p_partkey = ps_partkey)),
                          part,
                          partsupp))))) as s5,
            select([p_type, p_brand, p_size],
              filter((not((p_brand = "")) &&
                     (not((strpos(p_type, "") = 1)) &&
                     ((p_size = 0) ||
                     ((p_size = 0) ||
                     ((p_size = 0) ||
                     ((p_size = 0) ||
                     ((p_size = 0) ||
                     ((p_size = 0) || ((p_size = 0) || (p_size = 0)))))))))),
                atuple([ascalar(s5.p_brand), ascalar(s5.p_type),
                        ascalar(s5.p_size)],
                  cross))))))) |}]
