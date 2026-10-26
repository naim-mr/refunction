(* Instantiates the law functors on every domain and runs them.
   [dune test], or [dune exec tests/alcotest/test_domains.exe -- test <group>]. *)

open Domains
open Abstract_syntax
open Helpers
module B = AP_Partition.B
module O = AP_Partition.O
module P = AP_Partition.P
module AP = AP_Affines.AP

(* Mixed cases: bounds on one variable, relational, redundant, unsatisfiable. *)
let constraints =
  [
    cons [ (1, x) ] 0;
    (* x >= 0 *)
    cons [ (-1, x) ] 3;
    (* x <= 3 *)
    cons [ (1, y) ] (-2);
    (* y >= 2 *)
    cons [ (1, x); (-1, y) ] 0;
    (* x >= y *)
    cons [ (2, x); (1, y) ] 1;
    (* 2x + y >= -1 *)
    cons [ (-1, x); (-1, y) ] 10;
    (* x + y <= 10 *)
  ]

(* Partitions that are nested, overlapping or disjoint, plus top and bot. The
   list is rebuilt with each instance's [inner], since partition types differ. *)
let partitions inner top bot =
  [
    top;
    bot;
    inner [ cons [ (1, x) ] 0; cons [ (-1, x) ] 3 ];
    (* 0 <= x <= 3 *)
    inner [ cons [ (1, x) ] (-1); cons [ (-1, x) ] 2 ];
    (* 1 <= x <= 2 *)
    inner [ cons [ (1, x) ] (-2); cons [ (-1, x) ] 5 ];
    (* 2 <= x <= 5 *)
    inner [ cons [ (1, x) ] (-10) ];
    (* x >= 10 *)
    inner [ cons [ (1, x); (-1, y) ] 0; cons [ (1, y) ] 0 ];
    (* x >= y >= 0 *)
  ]

(* Assignments: shift, copy, relational (not exact in box/oct),
   non-deterministic. *)
let assigns =
  [
    (var x, bin A_PLUS (var x) (cst 1));
    (* x := x + 1 *)
    (var x, var y);
    (* x := y *)
    (var x, bin A_MINUS (bin A_MULTIPLY (cst 2) (var x)) (var y));
    (* x := 2x - y *)
    (var y, itv 0 3);
    (* y := [0,3] *)
  ]

(* Filters: bound, strict relational, sum, conjunction, disjunction. *)
let filters =
  [
    cmp A_GREATER_EQUAL (var x) (cst 2);
    (* x >= 2 *)
    cmp A_GREATER (var x) (var y);
    (* x > y *)
    cmp A_LESS_EQUAL (bin A_PLUS (var x) (var y)) (cst 4);
    (* x + y <= 4 *)
    cmp A_AND
      (cmp A_GREATER_EQUAL (var x) (cst 1))
      (cmp A_LESS_EQUAL (var x) (cst 2));
    (* 1 <= x && x <= 2 *)
    cmp A_OR (cmp A_LESS (var x) (cst 0)) (cmp A_GREATER (var y) (cst 3));
    (* x < 0 || y > 3 *)
  ]

module CL =
  Constraint_laws.Make
    (C)
    (struct
      let name = "linear"
      let env = env
      let samples = constraints
    end)

module PL_B =
  Partition_laws.Make
    (B)
    (struct
      let name = "box"
      let env = env
      let samples = partitions (B.inner env) (B.top env) (B.bot env)
      let constraints = constraints
      let assigns = assigns
      let filters = filters
    end)

module PL_O =
  Partition_laws.Make
    (O)
    (struct
      let name = "oct"
      let env = env
      let samples = partitions (O.inner env) (O.top env) (O.bot env)
      let constraints = constraints
      let assigns = assigns
      let filters = filters
    end)

module PL_P =
  Partition_laws.Make
    (P)
    (struct
      let name = "poly"
      let env = env
      let samples = partitions (P.inner env) (P.top env) (P.bot env)
      let constraints = constraints
      let assigns = assigns
      let filters = filters
    end)

(* Function samples on the support 0 <= x <= 3, rebuilt for each FUNCTION
   instance: constants 0, 1, 2, a function depending on x built by [extend]
   from x = 0 ↦ 0 and x = 3 ↦ 1 (see Regressions: today it is x, not x/3),
   its successor, bot and top. *)
module Function_samples
    (F : Ranking.FUNCTION)
    (I : sig
      val env : F.env
      val inner : C.t list -> F.B.t
    end) =
struct
  let name_support = I.inner [ cons [ (1, x) ] 0; cons [ (-1, x) ] 3 ]
  let zero = F.zero I.env

  let slope =
    F.extend
      (I.inner [ cons [ (1, x) ] 0; cons [ (-1, x) ] 0 ])
      (I.inner [ cons [ (1, x) ] (-3); cons [ (-1, x) ] 3 ])
      zero (F.successor zero)

  let samples =
    [
      zero;
      F.successor zero;
      F.successor (F.successor zero);
      slope;
      F.successor slope;
      F.bot I.env;
      F.top I.env;
    ]
end

module Function_instance
    (F : Ranking.FUNCTION)
    (I : sig
      val name : string
      val env : F.env
      val inner : C.t list -> F.B.t
    end) =
  Function_laws.Make
    (F)
    (struct
      module Sa = Function_samples (F) (I)

      let name = I.name
      let env = I.env
      let support = Sa.name_support
      let samples = Sa.samples
    end)

module Ord (F : Ranking.FUNCTION) =
  AP_Ordinals.AP_OrdinalValued
    (struct
      let ordmax = 2
    end)
    (F)

module FL_AB =
  Function_instance
    (AP_Affines.AB)
    (struct
      let name = "affine/box"
      let env = env
      let inner = B.inner env
    end)

module FL_AO =
  Function_instance
    (AP_Affines.AO)
    (struct
      let name = "affine/oct"
      let env = env
      let inner = O.inner env
    end)

module FL_AP =
  Function_instance
    (AP)
    (struct
      let name = "affine/poly"
      let env = env
      let inner = P.inner env
    end)

module FL_OAP =
  Function_instance
    (Ord
       (AP))
       (struct
         let name = "ordinal/poly"
         let env = env
         let inner = P.inner env
       end)

let () =
  Alcotest.run "domains"
    [
      ("constraint", CL.tests);
      ("partition", PL_B.tests @ PL_O.tests @ PL_P.tests);
      ("function", FL_AB.tests @ FL_AO.tests @ FL_AP.tests @ FL_OAP.tests);
      ("regressions", Regressions.tests);
      ("shadow", Shadow.tests);
    ]
