(***************************************************)
(*                                                 *)
(*   Trivial boolean constraint domain (top/bot)   *)
(*                                                 *)
(*  Test that Decision_Tree only depends on the    *)
(*  generic CONSTRAINT / PARTITION / FUNCTION      *)
(*  signatures, i.e. is independent of APRON.      *)
(*                                                 *)
(***************************************************)

open Constraints
open Domain
open Ranking
open Typed_syntax

(** A degenerate constraint domain with only two elements: [true] (satisfiable /
    top, "no information") and [false] (unsatisfiable / bottom). It contains no
    APRON type whatsoever, so instantiating [Decision_Tree] on top of it proves
    that the decision-tree functor is parametric in a plain [CONSTRAINT]. *)
module Bool_Constraint : CONSTRAINT = struct
  type cons = bool
  type env = unit
  type t = { cons : cons; env : env }
  type dim = var

  let init_env () = ()
  let env t = t.env
  let set_env env t = { t with env }
  let add_dim_to_env env _ = env
  let remove_dim_of_env env _ = env
  let make_unsat env = { cons = false; env }
  let is_bot t = not t.cons
  let compare t1 t2 = Bool.compare t1.cons t2.cons
  let is_eq t1 t2 = t1.cons = t2.cons

  (* [is_leq t1 t2] : t1 implies t2. bottom (false, empty set) implies
     everything; top (true, whole space) implies only top. *)
  let is_leq t1 t2 = (not t1.cons) || t2.cons
  let var _ _ = false
  let similar t1 t2 = t1.cons = t2.cons
  let negate t = { t with cons = not t.cons }
  let expand t = (t, t)
  let print fmt t = Format.fprintf fmt "%s" (if t.cons then "true" else "false")
end

(** A partition over {!Bool_Constraint}: it is itself boolean, [true] being the
    reachable top and [false] the empty (unsat) partition. *)
module Bool_Partition : PARTITION = struct
  module C = Bool_Constraint

  type env = unit
  type dim = C.dim
  type t = bool

  let bot () = false
  let top () = true
  let is_bot t = not t
  let is_leq _ t1 t2 = (not t1) || t2
  let join _ t1 t2 = t1 || t2
  let meet _ t1 t2 = t1 && t2
  let widen ?jokers:_ t1 t2 = t1 || t2
  let init_env () = ()
  let env _ = ()
  let set_env _ t = t
  let add_dim_to_env t _ = t
  let dim_in_env _ _ = true
  let remove_dim_of_env t _ = t
  let print fmt t = Format.fprintf fmt "%s" (if t then "TOP" else "BOT")
  let is_representable _ = true
  let constraints t = if t then [] else [ (C.make_unsat (C.init_env ())).cons ]
  let conjunction t = if t then [] else [ C.make_unsat (C.init_env ()) ]
  let assume ?pow:_ t = (t, t)
  let inner _ cs = not (List.exists C.is_bot cs)
  let bwd_assign ?controllable:_ t _ = t
  let ubwd_assign t _ = t
  let fwd_assign t _ = t
  let fwd_filter ?controllable:_ t _ = t
  let ubwd_filter t _ = t
end

(** A trivial leaf-function domain over {!Bool_Partition}: [true] = defined,
    [false] = bottom. *)
module Bool_Function : FUNCTION = struct
  module B = Bool_Partition

  type env = B.env
  type dim = B.dim
  type rank = unit
  type t = bool

  let init_env () = B.init_env ()
  let env _ = B.init_env ()
  let set_env _ t = t
  let bot _ = false
  let top _ = true
  let is_bot t = not t
  let is_top t = t
  let is_leq _ _ t1 t2 = (not t1) || t2
  let is_eq _ t1 t2 = t1 = t2
  let domain_eq d _ _ = d
  let join ?random:_ _ _ t1 t2 = t1 || t2
  let widen ?jokers:_ _ t1 t2 = t1 || t2
  let bwd_assign t _ = t
  let filter t _ = t
  let reinit _ = false
  let zero _ = true
  let defined t = t
  let plus _ t1 t2 = t1 || t2
  let extend _ _ t1 _ = t1
  let learn _ t1 _ = t1
  let reset t = t
  let predecessor t = t
  let successor t = t
  let print fmt t = Format.fprintf fmt "%s" (if t then "DEF" else "UNDEF")
end

module TS_Bool = Decision_Tree.Decision_Tree (Bool_Function)
(** The proof: a decision tree whose underlying constraint domain is the plain,
    APRON-free {!Bool_Constraint}. *)
