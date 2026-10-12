(* Laws of a FUNCTION, on a support partition. FUNCTION only builds constants
   ([zero], [successor], ...): a function depending on a variable comes from
   [extend] on two disjoint partitions, or from [bwd_assign]. The laws below do
   not depend on the meaning of [kind] in [is_leq] and [join]. *)

open Ranking

module Make
    (F : FUNCTION) (S : sig
      val name : string
      val env : F.env
      val support : F.B.t
      val samples : F.t list
    end) : Law.S = struct
  let case = Law.case S.name
  let eq = F.is_eq S.support
  let defined = List.filter F.defined S.samples

  let bot_top () =
    Law.holds "is_bot bot, is_top top"
      (F.is_bot (F.bot S.env) && F.is_top (F.top S.env))

  let zero_defined () = Law.holds "defined (zero env)" (F.defined (F.zero S.env))
  let eq_refl () = Law.holds "f = f" (Law.forall defined (fun f -> eq f f))

  let eq_sym () =
    Law.holds "f = g iff g = f"
      (Law.forall2 defined (fun f g -> eq f g = eq g f))

  let pred_succ () =
    Law.holds "predecessor (successor f) = f"
      (Law.forall defined (fun f -> eq (F.predecessor (F.successor f)) f))

  let succ_pred () =
    Law.holds "successor (predecessor f) = f"
      (Law.forall defined (fun f -> eq (F.successor (F.predecessor f)) f))

  let succ_differs () =
    Law.holds "successor f <> f"
      (Law.forall defined (fun f -> not (eq (F.successor f) f)))

  let reinit_bot () =
    Law.holds "reinit f is bot" (Law.forall S.samples (fun f -> F.is_bot (F.reinit f)))

  let tests =
    [
      case "bot and top" bot_top;
      case "zero defined" zero_defined;
      case "is_eq reflexive" eq_refl;
      case "is_eq symmetric" eq_sym;
      case "predecessor after successor" pred_succ;
      case "successor after predecessor" succ_pred;
      case "successor changes f" succ_differs;
      case "reinit is bot" reinit_bot;
    ]
end
