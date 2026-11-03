open Typed_syntax
open Apron
open Sig.Ranking
open Tast_to_texpr
open Utils
open Apron_utils
open Sig
open Sig.Domain
open AP_Partition


(** [VALUE]: operations on defined rankings, relative to the domain [B.t] or
    the environment [B.env] on which they are defined. [None] stands for a
    loss of precision (lifted to [Top]). *)
module type Value = sig
  module B : PARTITION

  type value

  val zero : B.env -> value
  val is_leq : B.t -> value -> value -> bool
  val is_eq : B.t -> value -> value -> bool
  val domain_eq : B.t -> value -> value -> B.t
  val min : B.t -> value -> value -> value option
  val max : B.t -> value -> value -> value option
  val widen : B.t -> value -> value -> value option
  val learn : B.t -> value -> value -> value option
  val extend : B.t -> B.t -> value -> value -> value option
  val succ : value -> value
  val pred : value -> value
  val plus : B.t -> value -> value -> value
  val bwd_assign : B.env -> value -> expr typed * expr typed -> value option
  val print : B.env -> Format.formatter -> value -> unit
end

module Make (V : Value) :
  FUNCTION with module B = V.B = struct
  module B = V.B

  type env = B.env
  type dim = B.dim
  (** [rank]: [Bot] undefined function, [Top] undefined function due to
      precision losses, [Fun of V.t] defined functions with value defined in V
  *)
  type rank = Bot | Fun of V.value | Top

  type t = { ranking : rank; env : env }

  let init_env () = B.init_env ()
  let env f = f.env
  let set_env env f = { f with env }
  let bot e = { ranking = Bot; env = e }
  let top e = { ranking = Top; env = e }
  let zero e = { ranking = Fun (V.zero e); env = e }
  let is_bot f = match f.ranking with Bot -> true | _ -> false
  let defined f = match f.ranking with Fun _ -> true | _ -> false
  let is_top f = match f.ranking with Top -> true | _ -> false

  let reinit f =
    match f.ranking with Top -> { ranking = Bot; env = env f } | _ -> f

  let is_leq k b f1 f2 =
    match (f1.ranking, f2.ranking) with
    | Fun f, Fun g -> V.is_leq b f g
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
    | Fun f1, Fun f2 -> V.is_eq b f1 f2
    | Bot, Bot | Top, Top -> true
    | _ -> true

  let domain_eq b f1 f2 =
    (* b = domain of first/second function, f1/f2 = value of first/second function *)
    match (f1.ranking, f2.ranking) with
    | Fun f1, Fun f2 -> V.domain_eq b f1 f2
    | Bot, Bot | Top, Top -> b
    | _ -> B.bot (B.env b)
  let of_option o = Option.fold ~none:Top ~some:(fun r -> Fun r) o

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
        | RESILIENCE -> {f1 with ranking = of_option (V.min b f g)}
        | APPROXIMATION | COMPUTATIONAL -> {f1 with ranking = of_option (V.max b f g)}
        )
    | _ -> top f1.env

  let widen ?(jokers = 0) b f1 f2 =
    match (f1.ranking, f2.ranking) with
    | Fun f , Fun g  -> {f1 with ranking = of_option (V.widen b g f)}
    | Bot, _ -> f2
    | _, Bot -> f1
    | _ -> top f1.env

  let lift1 op f =
    match f.ranking with Fun g -> { f with ranking = Fun (op g) } | _ -> f

  let lift2 op f1 f2 =
    match (f1.ranking, f2.ranking) with
    | Fun f, Fun g -> { f1 with ranking = Fun (op f g) }
    | _, Bot | Bot, _ -> bot f1.env
    | _, Top | Top, _ -> top f1.env

  let predecessor = lift1 V.pred
  let successor = lift1 V.succ
  let bwd_assign f _ = successor f
  let filter f _ = successor f
  let plus b f1 f2 = lift2 (V.plus b) f1 f2
  let extend _ _ _ _ = failwith "nyi"
  let learn _ _ _ = failwith "nyi"
  let reset f = zero f.env

  let print fmt f =
    match f.ranking with
    | Fun r -> V.print f.env fmt r
    | Bot -> Format.fprintf fmt "bottom"
    | Top -> Format.fprintf fmt "top"
end

