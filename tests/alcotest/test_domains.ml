(* Instantiates the law functors on every domain and runs them.
   [dune test], or [dune exec tests/alcotest/test_domains.exe -- test <group>]. *)

open Domains
open Helpers
module B = AP_Partition.B
module O = AP_Partition.O
module P = AP_Partition.P
module AP = AP_Affines.AP

(* Mixed cases: bounds on one variable, relational, redundant, unsatisfiable. *)
let constraints =
  [
    cons [ (1, x) ] 0;                 (* x >= 0 *)
    cons [ (-1, x) ] 3;                (* x <= 3 *)
    cons [ (1, y) ] (-2);              (* y >= 2 *)
    cons [ (1, x); (-1, y) ] 0;        (* x >= y *)
    cons [ (2, x); (1, y) ] 1;         (* 2x + y >= -1 *)
    cons [ (-1, x); (-1, y) ] 10;      (* x + y <= 10 *)
  ]

(* Partitions that are nested, overlapping or disjoint, plus top and bot. The
   list is rebuilt with each instance's [inner], since partition types differ. *)
let partitions inner top bot =
  [
    top;
    bot;
    inner [ cons [ (1, x) ] 0; cons [ (-1, x) ] 3 ];            (* 0 <= x <= 3 *)
    inner [ cons [ (1, x) ] (-1); cons [ (-1, x) ] 2 ];         (* 1 <= x <= 2 *)
    inner [ cons [ (1, x) ] (-2); cons [ (-1, x) ] 5 ];         (* 2 <= x <= 5 *)
    inner [ cons [ (1, x) ] (-10) ];                            (* x >= 10 *)
    inner [ cons [ (1, x); (-1, y) ] 0; cons [ (1, y) ] 0 ];    (* x >= y >= 0 *)
  ]

module CL = Constraint_laws.Make (C) (struct
  let name = "linear"
  let env = env
  let samples = constraints
end)

module PL_B = Partition_laws.Make (B) (struct
  let name = "box"
  let env = env
  let samples = partitions (B.inner env) (B.top env) (B.bot env)
  let constraints = constraints
end)

module PL_O = Partition_laws.Make (O) (struct
  let name = "oct"
  let env = env
  let samples = partitions (O.inner env) (O.top env) (O.bot env)
  let constraints = constraints
end)

module PL_P = Partition_laws.Make (P) (struct
  let name = "poly"
  let env = env
  let samples = partitions (P.inner env) (P.top env) (P.bot env)
  let constraints = constraints
end)

module FL_AP = Function_laws.Make (AP) (struct
  let name = "affine/poly"
  let env = env
  let support = P.inner env [ cons [ (1, x) ] 0; cons [ (-1, x) ] 3 ]
  let zero = AP.zero env

  let samples =
    [ zero; AP.successor zero; AP.successor (AP.successor zero); AP.bot env; AP.top env ]
end)

let () =
  Alcotest.run "domains"
    [
      ("constraint", CL.tests);
      ("partition", PL_B.tests @ PL_O.tests @ PL_P.tests);
      ("function", FL_AP.tests);
      ("regressions", Regressions.tests);
    ]
