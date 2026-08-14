open Apron
(** Constraint domain The signature [CONSTRAINT] define the domain of constraint
    that can be used to partition a Decision Tree *)

open Abstract_syntax
open Typed_syntax

module type CONSTRAINT = sig
  type cons
  (** Type defining the constraint. *)

  type env
  (** Type representing the environment in which the constraint is defined. *)

  type t = { cons : cons; env : env }
  (** Type representing the constraint alongside with its environment. *)

  type dim = var

  val init_env : unit -> env
  (** [init env ()] returns an empty env *)

  val env : t -> env
  (** [env t] returns the environment in which is defined the partition *)

  val set_env : env -> t -> t
  (** [update_env env t] returns [t] with the environment [env]*)

  val add_dim_to_env : env -> dim -> env
  (** [add_dim_to_env env x] add the dimension [x] inside the environment [env]*)

  val remove_dim_of_env : env -> dim -> env
  (** [remove_dim_of_env env x] remove the dimension [x] inside the environment
      [env]*)

  val make_unsat : env -> t
  (** [make_unsat env] returns a non satisfiable constraints over the
      environment [env]. *)

  val is_bot : t -> bool
  (** [is_bot t] tests if [t] is unsat. *)

  val compare : t -> t -> int
  (** [compare t1 t2] is the TOTAL order on constraints: negative if [t1] comes
      first, 0 if equal, positive otherwise. It is the primitive from which
      [is_eq] and [is_leq] derive, and it is what keeps decision-tree nodes
      canonically ordered. *)

  val is_eq : t -> t -> bool
  (** [is_eq t1 t2] tests if two constraints are equal: [compare t1 t2 = 0]. *)

  val is_leq : t -> t -> bool
  (** [is_leq t1 t2] is the order of {!compare}: [compare t1 t2 <= 0]. It must
      be total — for every [c], one of [is_leq c (negate c)] and
      [is_leq (negate c) c] holds, which is what makes a constraint and its
      negation collapse to the same canonical node. *)

  val var : var -> t -> bool
  (** [var v t] tests if [v] is constrained in [t]. *)

  val similar : t -> t -> bool
  (** [similar t1 t2] tests if two constraints are equal UP TO THEIR CONSTANT
      term, which is what lets the tree merge two nodes differing only by that
      constant. Reflexive, symmetric, implied by [is_eq]. *)

  val negate : t -> t
  (** [negate t] returns the negation of [t].

      CONTRACT — the negation must be EXACT, not an over-approximation:
      [t ∧ negate t = ⊥] and [t ∨ negate t = ⊤]. A decision-tree node stores
      the pair [(c, negate c)] and its two branches are meant to partition the
      state space; an inexact negation makes the two branches either overlap
      (unsound joins) or miss states (unsound coverage). [negate (negate t)]
      must also be [t], up to normalisation.

      This means the constraint domain has to be CLOSED UNDER COMPLEMENT, which
      is a real restriction on what can be plugged in here:
      - parity, congruence mod 2: [¬(x ≡ 0 [2])] is [x ≡ 1 [2]] — fine;
      - congruence mod 3: [¬(x ≡ 0 [3])] is [x ≡ 1 ∨ x ≡ 2] — NOT a single
        constraint, so such a domain cannot be used as a node constraint as is.
        It needs either a disjunctive node type, or to be carried in a product
        beside a complement-closed domain.

      The type system cannot enforce any of this. The law is checked instead by
      the domain test harness (see domains/todo.md §4.1). *)

  val expand : t -> t * t
  (** [expand t] transforms equalities in pairs of supeq and infeq. *)

  val print : Format.formatter -> t -> unit
end

type lincons_env = { vars : var list; ap_env : Environment.t }

module type AP_CONSTRAINT = sig
  include CONSTRAINT with type env = lincons_env and type cons = Lincons1.t

  val linexpr : t -> Linexpr1.t
  (** [linexpr t] returns the linear expression of [t]. APRON-specific, hence
      declared here rather than in {!CONSTRAINT}: a congruence or a boolean
      predicate has no meaningful linearisation. *)
end
