open Typed_syntax
open Sig.Ranking
open Tast_to_texpr
open Utils
open Sig
open Sig.Domain
open Z

module Make (B : PARTITION) : FUNCTION with module B = B = struct
  module B = B

  type env = B.env
  type dim = B.dim

  (** [rank]: [Bot] undefined function, [Top] undefined function due to
      precision losses, [Fun of Z.t] Constant function*)
  type rank = Bot | Fun of Z.t | Top

  type t = { ranking : rank; env : env }

  let init_env () = B.init_env ()
  let env f = f.env
  let set_env env f = { f with env }
  let bot e = { ranking = Bot; env = e }
  let top e = { ranking = Top; env = e }
  let zero e = { ranking = Fun Z.zero; env = e }
  let is_bot f = match f.ranking with Bot -> true | _ -> false
  let defined f = match f.ranking with Fun _ -> true | _ -> false
  let is_top f = match f.ranking with Top -> true | _ -> false

  let reinit f =
    match f.ranking with Top -> { ranking = Bot; env = env f } | _ -> f

  let is_leq k b f1 f2 =
    match (f1.ranking, f2.ranking) with
    | Fun f1, Fun f2 -> if Z.compare f1 f2 < 0 then false else true
    | Bot, Fun _ -> (
        match k with
        | APPROXIMATION -> false
        | COMPUTATIONAL -> true
        | RESILIENCE -> true)
    | Fun _, Bot -> (
        match k with
        | APPROXIMATION -> true
        | COMPUTATIONAL -> false
        | RESILIENCE -> false)
    | Fun _, Top -> (
        match k with
        | APPROXIMATION -> true
        | COMPUTATIONAL -> true
        | RESILIENCE -> false)
    | Top, Fun _ -> (
        match k with
        | APPROXIMATION -> false
        | COMPUTATIONAL -> false
        | RESILIENCE -> true)
    | Bot, _ | _, Top -> true
    | _ -> false

  let is_eq b f1 f2 =
    match (f1.ranking, f2.ranking) with
    | Fun f1, Fun f2 -> Z.compare f1 f2 = 0
    | Bot, Bot | Top, Top -> true
    | _ -> true

  let domain_eq b f1 f2 =
    (* b = domain of first/second function, f1/f2 = value of first/second function *)
    match (f1.ranking, f2.ranking) with
    | Fun f1, Fun f2 -> if Z.compare f1 f2 = 0 then b else B.bot (B.env b)
    | Bot, Bot | Top, Top -> b
    | _ -> B.bot (B.env b)

  let join k b f1 f2 =
    match (f1.ranking, f2.ranking) with
    | Bot, _ -> (
        match k with
        | RESILIENCE -> f2
        | APPROXIMATION -> f1
        | COMPUTATIONAL -> f2)
    | _, Bot -> (
        match k with
        | RESILIENCE -> f1
        | APPROXIMATION -> f2
        | COMPUTATIONAL -> f1)
    | Fun f, Top | Top, Fun f -> (
        match k with
        | RESILIENCE -> { ranking = Fun f; env = f1.env }
        | APPROXIMATION -> top f1.env
        | COMPUTATIONAL -> top f1.env)
    | Fun f, Fun g -> (
        match k with
        | RESILIENCE -> if Z.compare f g <= 0 then f1 else f2
        | APPROXIMATION | COMPUTATIONAL -> if Z.compare f g <= 0 then f1 else f2
        )
    | _ -> top f1.env

  let widen ?(jokers = 0) b f1 f2 =
    match (f1.ranking, f2.ranking) with
    | Bot, _ -> f2
    | _, Bot -> f1
    | _ -> top f1.env

  let z_op1 op f =
    match f.ranking with Fun g -> { f with ranking = Fun (op g) } | _ -> f

  let z_op2 op f1 f2 =
    match (f1.ranking, f2.ranking) with
    | Fun f, Fun g -> { f1 with ranking = Fun (op f g) }
    | _, Bot | Bot, _ -> bot f1.env
    | _, Top | Top, _ -> top f1.env

  let predecessor = z_op1 Z.pred
  let successor = z_op1 Z.succ
  let bwd_assign f _ = successor f
  let filter f _ = successor f
  let plus _ f1 f2 = z_op2 Z.( + ) f1 f2
  let extend _ _ _ _ = failwith "nyi"
  let learn _ _ _ = failwith "nyi"
  let reset f = zero f.env

  let print fmt f =
    match f.ranking with
    | Fun f -> Format.fprintf fmt "%s" (Z.to_string f)
    | Bot -> Format.fprintf fmt "bottom"
    | Top -> Format.fprintf fmt "top"
end
