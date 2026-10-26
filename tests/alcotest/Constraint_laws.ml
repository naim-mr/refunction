(* Laws of a CONSTRAINT: total order, exact negation, [similar], bot, print. *)

open Constraints

module Make
    (C : CONSTRAINT)
    (S : sig
      val name : string
      val env : C.env
      val samples : C.t list
    end) : Law.S = struct
  let case = Law.case S.name
  let sign n = compare n 0

  let compare_refl () =
    Law.holds "compare c c = 0"
      (Law.forall S.samples (fun c -> C.compare c c = 0))

  let compare_antisym () =
    Law.holds "sign (compare a b) = - sign (compare b a)"
      (Law.forall2 S.samples (fun a b ->
           sign (C.compare a b) = -sign (C.compare b a)))

  let compare_trans () =
    Law.holds "a <= b and b <= c imply a <= c"
      (Law.forall2 S.samples (fun a b ->
           Law.forall S.samples (fun c ->
               (not (C.compare a b <= 0 && C.compare b c <= 0))
               || C.compare a c <= 0)))

  let is_eq_compare () =
    Law.holds "is_eq a b iff compare a b = 0"
      (Law.forall2 S.samples (fun a b -> C.is_eq a b = (C.compare a b = 0)))

  let total () =
    Law.holds "c <= negate c or negate c <= c"
      (Law.forall S.samples (fun c ->
           C.is_leq c (C.negate c) || C.is_leq (C.negate c) c))

  let negate_involutive () =
    Law.holds "negate (negate c) = c"
      (Law.forall S.samples (fun c -> C.is_eq (C.negate (C.negate c)) c))

  let similar_refl () =
    Law.holds "similar c c" (Law.forall S.samples (fun c -> C.similar c c))

  let similar_sym () =
    Law.holds "similar a b iff similar b a"
      (Law.forall2 S.samples (fun a b -> C.similar a b = C.similar b a))

  let eq_implies_similar () =
    Law.holds "is_eq a b implies similar a b"
      (Law.forall2 S.samples (fun a b -> (not (C.is_eq a b)) || C.similar a b))

  let unsat_is_bot () =
    Law.holds "is_bot (make_unsat env)" (C.is_bot (C.make_unsat S.env))

  let print_total () =
    Law.forall S.samples (fun c ->
        ignore (Format.asprintf "%a" C.print c);
        true)
    |> Law.holds "print does not raise"

  let tests =
    [
      case "compare reflexive" compare_refl;
      case "compare antisymmetric" compare_antisym;
      case "compare transitive" compare_trans;
      case "is_eq is compare = 0" is_eq_compare;
      case "order total wrt negate" total;
      case "negate involutive" negate_involutive;
      case "similar reflexive" similar_refl;
      case "similar symmetric" similar_sym;
      case "is_eq implies similar" eq_implies_similar;
      case "make_unsat is bot" unsat_is_bot;
      case "print total" print_total;
    ]
end
