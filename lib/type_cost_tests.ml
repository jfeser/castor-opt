open Abslayout_load
open Castor_test.Test_util

open Type_cost.Make (struct
  let params = Set.empty (module Name)

  let cost_timeout = Some 60.0

  let cost_conn = Lazy.force tpch_conn
end)

let%expect_test "" =
  let r =
    load_string_exn (Lazy.force tpch_conn)
      {|
filter((sum_l_quantity > 0),
                ahashidx(dedup(
                           select([l_orderkey as k1],
                             groupby([l_orderkey,
                                      sum(l_quantity) as sum_l_quantity],
                               [l_orderkey],
                               lineitem))) as s1,
                  alist(filter((s1.k1 = l_orderkey),
                          groupby([l_orderkey,
                                   sum(l_quantity) as sum_l_quantity],
                            [l_orderkey],
                            lineitem)) as s2,
                    atuple([ascalar(s2.sum_l_quantity)], cross)),
                  ""))
|}
  in
  Fmt.pr "%f" (cost r);
  [%expect {| 0.000000 |}]

let%expect_test "" =
  let r =
    load_string_exn (Lazy.force tpch_conn)
      {|
select([l_orderkey, sum_l_quantity],
                          ahashidx(dedup(
                                     select([l_orderkey as x483],
                                       dedup(select([l_orderkey], lineitem)))) as s37,
                            select([l_orderkey, sum_l_quantity],
                              aorderedidx(dedup(
                                            depjoin(dedup(
                                                      select([l_orderkey],
                                                        lineitem)) as s33,
                                              select([sum(l_quantity) as sum_l_quantity],
                                                filter((l_orderkey =
                                                       s33.l_orderkey),
                                                  lineitem)))) as s32,
                                alist(depjoin(filter((l_orderkey = s37.x483),
                                                dedup(
                                                  select([l_orderkey],
                                                    lineitem))) as k1,
                                        filter((sum_l_quantity =
                                               s32.sum_l_quantity),
                                          select([l_orderkey,
                                                  sum(l_quantity) as sum_l_quantity],
                                            filter((l_orderkey =
                                                   k1.l_orderkey),
                                              lineitem)))) as s44,
                                  atuple([ascalar(s44.l_orderkey),
                                          ascalar(s44.sum_l_quantity)],
                                    cross)),
                                > 0, )),
                            ""))
|}
  in
  Fmt.pr "%f" (cost r);
  [%expect {| 27.000000 |}]

let%expect_test "" =
  let r =
    load_string_exn (Lazy.force tpch_conn)
      {|
select([ps_partkey, value],
  ahashidx(dedup(select([n_name as nation_n_name_0], nation)) as s1,
    depjoin(select([(const34 * 0.0) as const4],
              ascalar((select([sum((ps_supplycost * ps_availqty))],
                         filter((n_name = s1.nation_n_name_0),
                           join((ps_suppkey = s_suppkey),
                             join((s_nationkey = n_nationkey),
                               supplier,
                               filter((n_name = s1.nation_n_name_0), nation)),
                             partsupp)))) as const34)) as s4,
      filter((value > s4.const4),
        alist(dedup(
                select([ps_partkey as k1_partsupp_ps_partkey],
                  join((ps_suppkey = s_suppkey),
                    join((s_nationkey = n_nationkey),
                      supplier,
                      filter((n_name = s1.nation_n_name_0), nation)),
                    partsupp))) as s2,
          alist(select([ps_partkey,
                        sum((ps_supplycost * ps_availqty)) as value],
                  filter((n_name = s1.nation_n_name_0),
                    filter((ps_partkey = s2.k1_partsupp_ps_partkey),
                      join((ps_suppkey = s_suppkey),
                        join((s_nationkey = n_nationkey),
                          supplier,
                          filter((n_name = s1.nation_n_name_0), nation)),
                        partsupp)))) as s3,
            atuple([ascalar(s3.ps_partkey), ascalar(s3.value)], cross))))),
    ""))
|}
  in
  Fmt.pr "%f" (cost r);
  [%expect {| 2684.000000 |}]

let%expect_test "" =
  let r =
    load_string_exn (Lazy.force tpch_conn)
      {|
depjoin(select([(select([(sum((ps_supplycost * ps_availqty)) * 0.0) as v],
                   ahashidx(dedup(
                              select([n_name as x2901],
                                dedup(
                                  select([n_name],
                                    join(((ps_suppkey = s_suppkey) && true),
                                      join((s_nationkey = n_nationkey),
                                        supplier,
                                        nation),
                                      partsupp))))) as s149,
                     alist(filter((n_name = s149.x2901),
                             select([n_name, ps_availqty, ps_supplycost],
                               join(((ps_suppkey = s_suppkey) && true),
                                 join((s_nationkey = n_nationkey),
                                   supplier,
                                   nation),
                                 partsupp))) as s136,
                       atuple([ascalar(s136.ps_availqty),
                               ascalar(s136.ps_supplycost)],
                         cross)),
                     ""))) as q1],
          ascalar(false as dummy0)) as s93,
  alist(dedup(
          select([ps1_partkey],
            join(((ps1_suppkey = s1_suppkey) && true),
              join((s1_nationkey = n1_nationkey),
                select([s_nationkey as s1_nationkey, s_suppkey as s1_suppkey],
                  supplier),
                select([n_nationkey as n1_nationkey, n_name as n1_name],
                  nation)),
              select([ps_suppkey as ps1_suppkey, ps_partkey as ps1_partkey,
                      ps_supplycost as ps1_supplycost,
                      ps_availqty as ps1_availqty],
                partsupp)))) as k2,
    select([ps1_partkey, value],
      filter((value > s93.q1),
        select([ps1_partkey, sum((ps1_supplycost * ps1_availqty)) as value],
          ahashidx(dedup(
                     select([n_name as x1912],
                       dedup(select([n_name], nation)))) as s94,
            alist(join(((n1_name = s94.x1912) &&
                       ((ps1_partkey = k2.ps1_partkey) &&
                       (ps1_suppkey = s1_suppkey))),
                    join((s1_nationkey = n1_nationkey),
                      select([s_nationkey as s1_nationkey,
                              s_suppkey as s1_suppkey],
                        supplier),
                      select([n_nationkey as n1_nationkey, n_name as n1_name],
                        nation)),
                    select([ps_suppkey as ps1_suppkey,
                            ps_partkey as ps1_partkey,
                            ps_supplycost as ps1_supplycost,
                            ps_availqty as ps1_availqty],
                      partsupp)) as s81,
              atuple([ascalar(s81.ps1_partkey), ascalar(s81.ps1_supplycost),
                      ascalar(s81.ps1_availqty)],
                cross)),
            ""))))))
|}
  in
  Fmt.pr "%f" (cost r);
  [%expect {| 12974.000000 |}]

let%expect_test "" =
  let r =
    load_string_exn (Lazy.force tpch_conn)
      {|
select([s1_acctbal, s1_name, n1_name, p1_partkey, p1_mfgr, s1_address,
           s1_phone, s1_comment],
     ahashidx(depjoin(select([min(p_size) as lo, max(p_size) as hi],
                        dedup(select([p_size], part))) as k1,
                select([range as k0], range(k1.lo, k1.hi))) as s0,
       select([s1_acctbal, s1_name, n1_name, p1_partkey, p1_mfgr, s1_address,
               s1_phone, s1_comment],
         alist(filter((p1_size = s0.k0),
                 orderby([s1_acctbal desc, n1_name, s1_name, p1_partkey],
                   join((((r1_name = r_name) &&
                         (((ps_partkey = ps1_partkey) &&
                          (ps1_supplycost = min_cost)) &&
                         (ps1_supplycost = min_cost))) && true),
                     join((n1_regionkey = r1_regionkey),
                       select([r_name as r1_name, r_regionkey as r1_regionkey],
                         region),
                       join((s1_nationkey = n1_nationkey),
                         select([n_name as n1_name, n_nationkey as n1_nationkey,
                                 n_regionkey as n1_regionkey],
                           nation),
                         join((s1_suppkey = ps1_suppkey),
                           select([s_nationkey as s1_nationkey,
                                   s_suppkey as s1_suppkey,
                                   s_acctbal as s1_acctbal, s_name as s1_name,
                                   s_address as s1_address, s_phone as s1_phone,
                                   s_comment as s1_comment],
                             supplier),
                           join((p1_partkey = ps1_partkey),
                             select([p_size as p1_size, p_type as p1_type,
                                     p_partkey as p1_partkey, p_mfgr as p1_mfgr],
                               part),
                             select([ps_supplycost as ps1_supplycost,
                                     ps_partkey as ps1_partkey,
                                     ps_suppkey as ps1_suppkey],
                               partsupp))))),
                     depjoin(dedup(
                               select([r_name, ps_partkey],
                                 join((s_suppkey = ps_suppkey),
                                   join((s_nationkey = n_nationkey),
                                     join((n_regionkey = r_regionkey),
                                       nation,
                                       region),
                                     supplier),
                                   partsupp))) as k2,
                       select([r_name, ps_partkey,
                               min(ps_supplycost) as min_cost],
                         join((((r_name = k2.r_name) &&
                               (ps_partkey = k2.ps_partkey)) &&
                              (s_suppkey = ps_suppkey)),
                           join((s_nationkey = n_nationkey),
                             join((n_regionkey = r_regionkey), nation, region),
                             supplier),
                           partsupp)))))) as s1,
           filter(((r1_name = "") &&
                  (strpos(p1_type, "") =
                  ((strlen(p1_type) - strlen("")) + 1))),
             atuple([ascalar(s1.r1_name), ascalar(s1.n1_name),
                     ascalar(s1.s1_acctbal), ascalar(s1.s1_name),
                     ascalar(s1.s1_address), ascalar(s1.s1_phone),
                     ascalar(s1.s1_comment), ascalar(s1.p1_type),
                     ascalar(s1.p1_partkey), ascalar(s1.p1_mfgr)],
               cross)))),
       0))
|}
  in
  Fmt.pr "%f" (cost r);
  [%expect {| 7398.000000 |}]

let%expect_test "" =
  let r =
    load_string_exn (Lazy.force tpch_conn)
      {|
select([n1_name, n2_name, l_year, revenue],
   alist(orderby([n1_name, n2_name, l_year],
           dedup(
             select([n1_name, n2_name, to_year(l_shipdate) as l_year],
               join(((s_suppkey = l_suppkey) && true),
                 join((o_orderkey = l_orderkey),
                   join((c_custkey = o_custkey),
                     join((c_nationkey = n2_nationkey),
                       select([n_name as n2_name, n_nationkey as n2_nationkey], nation),
                       customer),
                     orders),
                   filter(((l_shipdate >= date("1995-01-01")) && (l_shipdate <= date("1996-12-31"))), lineitem)),
                 join((s_nationkey = n1_nationkey),
                   select([n_name as n1_name, n_nationkey as n1_nationkey], nation),
                   supplier))))) as k0,
     select([n1_name, n2_name, l_year, revenue],
       ahashidx(dedup(
                  atuple([dedup(
                            atuple([select([n_name as x27], dedup(select([n_name], nation))),
                                    select([n_name as x27], dedup(select([n_name], nation)))],
                              concat)),
                          dedup(
                            atuple([select([n_name as x30], dedup(select([n_name], nation))),
                                    select([n_name as x30], dedup(select([n_name], nation)))],
                              concat))],
                    cross)) as s7,
         alist(filter((count0 > 0),
                 select([count() as count0, n1_name, n2_name, to_year(l_shipdate) as l_year,
                         sum((l_extendedprice * (1 - l_discount))) as revenue],
                   atuple([ascalar(s7.x27), ascalar(s7.x30),
                           alist(filter((true && (n2_name = k0.n2_name)),
                                   select([n_name as n2_name, n_nationkey as n2_nationkey], nation)) as s4,
                             filter((((n1_name = s7.x27) && (n2_name = s7.x30)) ||
                                    ((n1_name = s7.x30) && (n2_name = s7.x27))),
                               atuple([ascalar(s4.n2_name),
                                       alist(select([l_suppkey, l_shipdate, l_discount, l_extendedprice],
                                               filter(((to_year(l_shipdate) = k0.l_year) &&
                                                      (c_nationkey = s4.n2_nationkey)),
                                                 select([l_suppkey, l_shipdate, 
                                                         l_discount, 
                                                         l_extendedprice, 
                                                         c_nationkey],
                                                   join((c_custkey = o_custkey),
                                                     join((o_orderkey = l_orderkey),
                                                       filter(((l_shipdate >= date("1995-01-01")) &&
                                                              (l_shipdate <= date("1996-12-31"))),
                                                         lineitem),
                                                       orders),
                                                     customer)))) as s3,
                                         atuple([atuple([ascalar(s3.l_shipdate), 
                                                         ascalar(s3.l_discount), 
                                                         ascalar(s3.l_extendedprice)],
                                                   cross),
                                                 alist(select([n1_name],
                                                         join((((n1_name = k0.n1_name) && (s_suppkey = s3.l_suppkey))
                                                              && (s_nationkey = n1_nationkey)),
                                                           select([n_name as n1_name, n_nationkey as n1_nationkey],
                                                             nation),
                                                           supplier)) as s2,
                                                   ascalar(s2.n1_name))],
                                           cross))],
                                 cross)))],
                     cross))) as s8,
           atuple([ascalar(s8.count0), ascalar(s8.n1_name), ascalar(s8.n2_name), 
                   ascalar(s8.l_year), ascalar(s8.revenue)],
      cross)),
         ("", "")))))
|}
  in
  Fmt.pr "%f" (cost r);
  [%expect {| 15151.000000 |}]
