(* Laws of a FUNCTION, on a support partition. FUNCTION only builds constants
   ([zero], [successor], ...): a function depending on a variable comes from
   [extend] on two disjoint partitions, or from [bwd_assign]. *)

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

  (* Order and join, per kind. On two defined functions [is_leq] is the
     pointwise order on the support whatever the kind; the kind only places
     Bot and Top. *)
  let kinds = Sig.Domain.[ COMPUTATIONAL; APPROXIMATION; RESILIENCE ]
  let leq k = F.is_leq k S.support
  let join k = F.join k S.support

  let leq_refl () =
    Law.holds "f <=_k f"
      (Law.forall kinds (fun k -> Law.forall S.samples (fun f -> leq k f f)))

  let leq_trans () =
    Law.holds "f <=_k g and g <=_k h imply f <=_k h"
      (Law.forall kinds (fun k ->
           Law.forall2 S.samples (fun f g ->
               Law.forall S.samples (fun h ->
                   (not (leq k f g && leq k g h)) || leq k f h))))

  (* For the approximation and resilience kinds, Bot and Top are incomparable:
     their join is not constrained. *)
  let incomparable k f g =
    k <> Sig.Domain.COMPUTATIONAL
    && ((F.is_bot f && F.is_top g) || (F.is_top f && F.is_bot g))

  (* The approximation join (not controllable) is an upper bound. *)
  let join_upper k () =
    Law.holds "f, g <=_k f ⊔_k g"
      (Law.forall2 S.samples (fun f g ->
           incomparable k f g
           ||
           let j = join k f g in
           leq k f j && leq k g j))

  let join_comm k () =
    Law.holds "f ⊔_k g = g ⊔_k f"
      (Law.forall2 S.samples (fun f g ->
           let j1 = join k f g and j2 = join k g f in
           leq k j1 j2 && leq k j2 j1))

  let join_idem k () =
    Law.holds "f ⊔_k f = f"
      (Law.forall S.samples (fun f ->
           let j = join k f f in
           leq k j f && leq k f j))

  (* The resilience join (controllable) under-approximates both defined
     functions, pointwise. *)
  let join_controllable_lower () =
    let open Sig.Domain in
    Law.holds "f ⊔c g <= f, g (pointwise, defined f g)"
      (Law.forall2 defined (fun f g ->
           let j = F.join ~controllable:true RESILIENCE S.support f g in
           (not (F.defined j)) || (leq COMPUTATIONAL j f && leq COMPUTATIONAL j g)))

  (* As for partitions, the second argument of widen is above the first. *)
  let widen_upper () =
    let open Sig.Domain in
    Law.holds "f, g <= f ∇ (f ⊔ g)"
      (Law.forall2 S.samples (fun f g ->
           let w = F.widen S.support f (join COMPUTATIONAL f g) in
           leq COMPUTATIONAL f w && leq COMPUTATIONAL g w))

  let per_kind name law =
    List.map
      (fun k ->
        let kn =
          match k with
          | Sig.Domain.COMPUTATIONAL -> "computational"
          | APPROXIMATION -> "approximation"
          | RESILIENCE -> "resilience"
        in
        case (name ^ " (" ^ kn ^ ")") (law k))
      kinds

  let tests =
    per_kind "join upper bound" join_upper
    @ per_kind "join commutative" join_comm
    @ per_kind "join idempotent" join_idem
    @ [
      case "is_leq reflexive" leq_refl;
      case "is_leq transitive" leq_trans;
      case "controllable join lower bound" join_controllable_lower;
      case "widen upper bound" widen_upper;
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
