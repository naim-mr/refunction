(* One test per known bug, checking exact values: the laws check properties, and
   miss for instance a join that returns a too large upper bound. *)

open Domains
open Helpers
module P = AP_Partition.P
module AP = AP_Affines.AP

(* Coefficient of # (AP_Affine): the hull of x = 0 ↦ 0 and x = 3 ↦ 1 is
   bounded by # <= x/3, which APRON returns as -3# + x >= 0; setting the
   coefficient of # to 0 reads f = x, so f(3) = 3 instead of 1. *)
let extend_slope () =
  let b1 = P.inner env [ cons [ (1, x) ] 0; cons [ (-1, x) ] 0 ] in
  let b2 = P.inner env [ cons [ (1, x) ] (-3); cons [ (-1, x) ] 3 ] in
  let zero = AP.zero env in
  let one = AP.successor zero in
  let f = AP.extend b1 b2 zero one in
  Law.holds "f = 0 on x = 0" (AP.is_eq b1 f zero);
  Law.holds "f = 1 on x = 3" (AP.is_eq b2 f one)

let tests = [ Law.case "affine/poly" "extend keeps the slope (# coefficient)" extend_slope ]
