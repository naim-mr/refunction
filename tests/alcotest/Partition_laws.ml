(* Laws of a PARTITION: lattice laws of join/meet, widen extensive, top/bot,
   exact negation of the constraints. PARTITION has no [is_eq]: equality is
   [is_leq] in both directions. *)

open Sig.Domain
open Ranking

module Make
    (B : PARTITION) (S : sig
      val name : string
      val env : B.env
      val samples : B.t list
      val constraints : B.C.t list
    end) : Law.S = struct
  let leq = B.is_leq COMPUTATIONAL
  let eq a b = leq a b && leq b a
  let join = B.join COMPUTATIONAL
  let meet = B.meet COMPUTATIONAL
  let case = Law.case S.name
  let top = B.top S.env
  let bot = B.bot S.env

  let leq_refl () = Law.holds "a <= a" (Law.forall S.samples (fun a -> leq a a))
  let bot_is_bot () = Law.holds "is_bot bot" (B.is_bot bot)
  let bot_least () = Law.holds "bot <= a" (Law.forall S.samples (fun a -> leq bot a))
  let top_greatest () = Law.holds "a <= top" (Law.forall S.samples (fun a -> leq a top))
  let inner_empty () = Law.holds "inner env [] = top" (eq (B.inner S.env []) top)

  let join_upper () =
    Law.holds "a, b <= a ⊔ b"
      (Law.forall2 S.samples (fun a b ->
           let j = join a b in
           leq a j && leq b j))

  let meet_lower () =
    Law.holds "a ⊓ b <= a, b"
      (Law.forall2 S.samples (fun a b ->
           let m = meet a b in
           leq m a && leq m b))

  let join_comm () =
    Law.holds "a ⊔ b = b ⊔ a"
      (Law.forall2 S.samples (fun a b -> eq (join a b) (join b a)))

  let meet_comm () =
    Law.holds "a ⊓ b = b ⊓ a"
      (Law.forall2 S.samples (fun a b -> eq (meet a b) (meet b a)))

  let join_idem () =
    Law.holds "a ⊔ a = a" (Law.forall S.samples (fun a -> eq (join a a) a))

  let meet_idem () =
    Law.holds "a ⊓ a = a" (Law.forall S.samples (fun a -> eq (meet a a) a))

  let leq_join () =
    Law.holds "a <= b implies a ⊔ b = b"
      (Law.forall2 S.samples (fun a b -> (not (leq a b)) || eq (join a b) b))

  (* APRON's widening requires its first argument below the second, as in the
     iterators: widen against a ⊔ b. *)
  let widen_upper () =
    Law.holds "a, b <= a ∇ (a ⊔ b)"
      (Law.forall2 S.samples (fun a b ->
           let w = B.widen a (join a b) in
           leq a w && leq b w))

  (* let negate_disjoint () =
    Law.holds "c ∧ negate c is bot"
      (Law.forall S.constraints (fun c ->
           B.is_bot (B.inner S.env [ c; B.C.negate c ]))) *)

  let negate_cover () =
    Law.holds "c ∨ negate c is top"
      (Law.forall S.constraints (fun c ->
           eq (join (B.inner S.env [ c ]) (B.inner S.env [ B.C.negate c ])) top))

  let tests =
    [
      case "is_leq reflexive" leq_refl;
      case "bot is bot" bot_is_bot;
      case "bot least" bot_least;
      case "top greatest" top_greatest;
      case "inner [] is top" inner_empty;
      case "join upper bound" join_upper;
      case "meet lower bound" meet_lower;
      case "join commutative" join_comm;
      case "meet commutative" meet_comm;
      case "join idempotent" join_idem;
      case "meet idempotent" meet_idem;
      case "a <= b implies a join b = b" leq_join;
      case "widen upper bound" widen_upper;
      case "negate disjoint" negate_disjoint;
      case "negate covers" negate_cover;
    ]
end
