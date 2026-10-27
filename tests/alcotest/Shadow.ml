(* C.shadow: elimination of x from b /\ inf <= x <= sup. The real shadow (k = 0)
   must be the APRON projection; the dark shadow (k a b = -(a-1)(b-1)) must be
   below it and contain only values of y with an integer witness x. *)

open Domains
open Helpers
open Typed_syntax
module P = AP_Partition.P

let one = Coeff.s_of_int 1
let real _ _ = Coeff.s_of_int 0

let dark a b =
  Coeff.neg
    (Utils.Apron_utils.mul_coeff
       (Utils.Apron_utils.sub_coeff a one)
       (Utils.Apron_utils.sub_coeff b one))

let fin n = Scalar.of_int n
let pinf = Scalar.of_infty 1
let minf = Scalar.of_infty (-1)
let shadow k cs inf sup = P.inner env (C.shadow k env cs x inf sup)
let eq a b = P.is_leq COMPUTATIONAL a b && P.is_leq COMPUTATIONAL b a

(* Non-unit coefficients, so that the dark shadow differs from the real one. *)
let samples =
  [
    [];
    (* top *)
    [ cons [ (1, x); (-1, y) ] 0 ];
    (* x >= y *)
    [ cons [ (1, x); (-1, y) ] 0; cons [ (1, y) ] (-2) ];
    (* x >= y >= 2 *)
    [ cons [ (2, x); (-1, y) ] 0; cons [ (-2, x); (1, y) ] 0 ];
    (* y = 2x *)
    [ cons [ (3, x); (-1, y) ] 0; cons [ (-3, x); (1, y) ] 1 ];
    (* 3x <= y + 1, y <= 3x *)
    [ cons [ (2, x); (-1, y) ] (-1); cons [ (-3, x); (1, y) ] 5 ];
    (* 2x >= y + 1, 3x <= y + 5 *)
  ]

let bounds = [ (fin 0, fin 3); (minf, pinf); (minf, fin 2); (fin 1, pinf) ]

let forall_cases p =
  List.for_all
    (fun cs -> List.for_all (fun (inf, sup) -> p cs inf sup) bounds)
    samples

(* Projection computed by APRON: forget x in b /\ inf <= x <= sup. *)
let projection cs inf sup =
  let bnd coef c =
    let t = cons [ (coef, x) ] 0 in
    Lincons1.set_cst t.cons (Coeff.Scalar c);
    t
  in
  let cs =
    (if Scalar.is_infty inf = 0 then [ bnd 1 (Scalar.neg inf) ] else [])
    @ (if Scalar.is_infty sup = 0 then [ bnd (-1) sup ] else [])
    @ cs
  in
  let man = Polka.manager_alloc_loose () in
  let a = Lincons1.array_make env.ap_env (List.length cs) in
  List.iteri (fun i (c : C.t) -> Lincons1.array_set a i c.cons) cs;
  let p = Abstract1.of_lincons_array man env.ap_env a in
  let p = Abstract1.forget_array man p [| apron_of_var x |] false in
  let a = Abstract1.to_lincons_array man p in
  P.ap_inner env (List.init (Lincons1.array_length a) (Lincons1.array_get a))

let real_is_projection () =
  Law.holds "real shadow = forget x"
    (forall_cases (fun cs inf sup ->
         eq (shadow real cs inf sup) (projection cs inf sup)))

let dark_below_real () =
  Law.holds "dark shadow <= real shadow"
    (forall_cases (fun cs inf sup ->
         P.is_leq COMPUTATIONAL (shadow dark cs inf sup)
           (shadow real cs inf sup)))

(* Every integer y of the dark shadow has an integer x in [inf, sup] with
   (x, y) in b. Enumerated on a window large enough for the samples. *)
let dark_integer_sound () =
  let point v n = [ cons [ (1, v) ] (-n); cons [ (-1, v) ] n ] in
  let range a b = List.init (b - a + 1) (fun i -> a + i) in
  let in_bounds inf sup n =
    (Scalar.is_infty inf <> 0 || Scalar.cmp_int inf n <= 0)
    && (Scalar.is_infty sup <> 0 || Scalar.cmp_int sup n >= 0)
  in
  Law.holds "dark shadow has integer witnesses"
    (forall_cases (fun cs inf sup ->
         let d = shadow dark cs inf sup in
         List.for_all
           (fun ny ->
             P.is_bot (P.meet COMPUTATIONAL d (P.inner env (point y ny)))
             || List.exists
                  (fun nx ->
                    in_bounds inf sup nx
                    && not
                         (P.is_bot (P.inner env (cs @ point x nx @ point y ny))))
                  (range (-30) 30))
           (range (-8) 8)))

let exact_values () =
  (* x >= y, x in [0, 3]: y <= 3 *)
  Law.holds "x >= y, x in [0,3] gives y <= 3"
    (eq
       (shadow real [ cons [ (1, x); (-1, y) ] 0 ] (fin 0) (fin 3))
       (P.inner env [ cons [ (-1, y) ] 3 ]));
  (* y = 2x, x unbounded: real shadow top, dark shadow bot (0 >= 1) *)
  let even = [ cons [ (2, x); (-1, y) ] 0; cons [ (-2, x); (1, y) ] 0 ] in
  Law.holds "y = 2x: real shadow is top"
    (eq (shadow real even minf pinf) (P.top env));
  Law.holds "y = 2x: dark shadow is bot" (P.is_bot (shadow dark even minf pinf))

let empty_conjunction () =
  Law.holds "shadow of top is top"
    (eq (shadow dark [] minf pinf) (P.top env)
    && eq (shadow dark [] (fin 0) (fin 3)) (P.top env))

let tests =
  [
    Law.case "linear" "shadow: real = projection" real_is_projection;
    Law.case "linear" "shadow: dark <= real" dark_below_real;
    Law.case "linear" "shadow: dark has integer witnesses" dark_integer_sound;
    Law.case "linear" "shadow: exact values" exact_values;
    Law.case "linear" "shadow: empty conjunction" empty_conjunction;
  ]
