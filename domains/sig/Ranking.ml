open Apron
open Domain
open Constraints
open Abstract_syntax
open Typed_syntax

(** Signature for a single partition of the domain of a ranking function. *)
module type PARTITION = sig
  module C : CONSTRAINT
  (** [module C] The underlying constraints domains, a parititon is a
      conjunction of such constraints *)

  include DOMAIN with type dim = C.dim

  val is_representable : expr -> bool
  (** [is_representable e] tests if the expression [e] is EXACTLY representable
      in the partition, i.e. assigning or filtering by [e] loses no precision.
      It is one half of the A-controlled condition (see [ATLIterator]: not
      tainted AND exactly representable), so it must only hold when it is
      true: [false] is always sound, at the cost of fewer A-controlled
      statements. *)

  val conjunction : t -> C.t list
  (** [conjunction t] returns [t] as a list of constraints in [C] (equalities
      expanded into pairs of inequalities when [C] supports it). Generic
      access to the constraints of a partition; [c.cons] gives the raw
      representation. *)

  val split : ?pow:float -> t -> t * t
  (** [split ~pow t] cuts [t] in two pieces [(t1, t2)]. Used by the
      conflict-driven analysis to split a piece where the ranking function is
      undefined and restart the analysis on each half.

      CONTRACT (checked by asserts in [Cda]): [t1 ⊔ t2 = t], and neither [t1]
      nor [t2] is bottom. [pow] steers where the cut is made. When no cut is
      possible, [(t, t)] is returned. *)

  val inner : env -> C.t list -> t
  (** [inner env cs] returns the partitions defined by the constraints in [cs]
      on [env]*)

  val bwd_assign : ?controllable:bool -> t -> expr typed * expr typed -> t
  (** [bwd_assign ~controllable t lv exp] Over-approximating backward
      assignement [lv := exp] on [t]. [controllable] (default [false]) tells
      whether the statement is A-controlled, i.e. not tainted and exactly
      representable. *)

  val ubwd_assign : t -> expr typed * expr typed -> t
  (** [ubwd_assign t lv exp] Under-approximating backward assignement
      [lv := exp] on [t]*)

  val fwd_assign : t -> expr typed * expr typed -> t
  (** [fwd_assign t lv exp] Over-approximating forward assignement [lv := exp]
      on [t]*)

  val fwd_filter : ?controllable:bool -> t -> expr typed -> t
  (** [fwd_filter ~controllable t exp] Over-approximating forward filter
      [exp != 0] on [t]. [controllable] (default [false]): same meaning as in
      [bwd_assign]. *)

  val ubwd_filter : t -> expr typed -> t
  (** [ubwd_assign t exp] Under-approximating backward filter [exp != 0] on [t]*)
end

(** The APRON numerical domain behind an [AP_NUMERICAL] instance. *)
type numerical = Boxes | Octagons | Polyhedra

(** [module type AP_NUMERICAL] include an apron domain type and a manager for it
*)
module type AP_NUMERICAL = sig
  type lib

  val kind : numerical
  (** [kind] which APRON domain this instance is, for the treatments that are
      specific to one of them. *)

  val manager : lib Manager.t
  val supports_underapproximation : bool

  val is_representable : expr -> bool
  (** [is_representable e] tests if [e] is exactly representable in the
      numerical domain (e.g. univariate for boxes, linear for polyhedra).
      [AP_Partition] forwards it as [PARTITION.is_representable]. *)
end

(** [module type AP_PARTITION] module type for [PARTITION] relying on APRON *)
module type AP_PARTITION = sig
  module C : AP_CONSTRAINT
  module N : AP_NUMERICAL
  include PARTITION with module C := C and type env = C.env

  val ap_env : env -> Environment.t
  val inner : env -> C.t list -> t

  val ap_constraints : t -> Lincons1.t list
  (** [ap_constraints t] returns the APRON (linear) projection of the partition,
      i.e. the numerical constraints usable by the affine ranking leaves. *)

  val ap_inner : env -> Lincons1.t list -> t
  (** [ap_inner env cs] builds a partition from APRON linear constraints (dual
      of [ap_constraints]); the non-numerical components are left at top. *)
end

module type FUNCTION = sig
  module B : PARTITION
  (** [module B] defines the domain on which the function is defined. *)

  type env = B.env
  (** Environement on which is defined the expression of function. *)

  type dim = B.dim
  (** Type of a dimension. *)

  type rank
  (** Type of an abstract expression for the function. *)

  type t
  (** Type of an abstract value. *)

  val init_env : unit -> env
  (** [init env ()] returns an empty env *)

  val env : t -> env
  (** [env t] returns the environment in which is defined the partition *)

  val set_env : env -> t -> t
  (** [update_env env t] returns [t] with the environment [env]*)

  val bot : env -> t
  (** [bot env] returns the bot element defines on [env]. *)

  val top : env -> t
  (** [top env] returns the top element defines on [env]. *)

  val is_bot : t -> bool
  (** [is_bot t] tests if [t] is equal to bot. *)

  val is_top : t -> bool
  (** [is_top t] tests if [t] is equal to top. *)

  val is_leq : kind -> B.t -> t -> t -> bool
  (** [is_leq kind domain t1 t2] checks if the function [t1] is less or equal
      than [t2] on the given [domain] *)

  val is_eq : B.t -> t -> t -> bool
  (** [is_eq kind domain t1 t2] returns the domains on which the functions [t1]
      and [t2] are equals *)

  val domain_eq : B.t -> t -> t -> B.t
  (** [domain_eq kind domain t1 t2] checks if the function [t1] is equal to [t2]
      on the given [domain] *)

  val join : ?controllable:bool -> kind -> B.t -> t -> t -> t
  (** [join ~controllable kind domain t1 t2] computes the join of the functions
      [t1] and [t2] on the given [domain]. [controllable] is the control of the
      statement being assigned: [true] (A-controlled) selects the resilience
      join, [false] (Ā-controlled, default) the approximation join, which is
      the sound default. *)

  val widen : ?jokers:int -> B.t -> t -> t -> t
  (** [widening domain t1 t2] compute the widening of function [t1] and the
      function [t2] on the given [domain] *)

  val bwd_assign : t -> expr typed * expr typed -> t
  (** [bwd_assign t lv exp] Over-approximating backward assignement [lv := exp]
      on the function [t]*)

  val filter : t -> expr typed -> t
  (** [bwd_assign t exp] Over-approximating backward filter [exp != 0] on [t]*)

  val reinit : t -> t
  (** [reinit t] set the function to bot *)

  val zero : env -> t
  (** [zero t env] return the constant function 0 on the environment [env]*)

  val defined : t -> bool
  (** [defined t] checks if the function [t] is a defined function *)

  val plus : B.t -> t -> t -> t
  (** [plus domain t1 t2] compute the sum of the function [t1] and [t2] on
      [domain] *)

  val extend : B.t -> B.t -> t -> t -> t
  (** [extends domain1 domain2 t1 t2] comment TODO *)

  val learn : B.t -> t -> t -> t
  (** [learn domain t1 t2] comment TODO *)

  val reset : t -> t
  (** [reset domain t] reset the expression of the function [t] on [domain] *)

  val predecessor : t -> t
  (** [predecessor t] -1 operator on the function [t] *)

  val successor : t -> t
  (** [successor t] +1 operator on the function [t] *)

  val print : Format.formatter -> t -> unit
  (** [print fmt t] pretty printer for the datatype t *)
end

module type RANKING_FUNCTION = sig
  module B : PARTITION
  (** [module B] defines the domain on which the function is defined. *)

  type env
  (** Environement on which is defined the expression of function. *)

  type dim = B.dim
  (** Type of a dimension. *)

  type t
  (** Type of an abstract value. *)
  val f_env : t -> B.env
  val env : t -> env
  (** [env t] returns the environment in which is defined the partition *)
  val bot : env -> t
  (** [bot env] returns the bot element defines on [env]. *)

  val top : env -> t
  (** [top env] returns the top element defines on [env]. *)

  val is_bot : t -> bool
  (** [is_bot t] tests if [t] is equal to bot. *)

  (** {2 Core} Used by every analysis (termination, ATL, CTL). *)

  val is_leq : kind -> t -> t -> bool
  val join : kind -> t -> t -> t
  val widen : ?jokers:int -> t -> t -> t
  val lift_fenv : B.env -> env
  val update_dom : B.t option -> env -> env
  val bwd_assign : ?domain:B.t -> ?controllable:bool -> t -> expr typed * expr typed -> t
  (** [bwd_assign ~controllable t (lv, exp)] backward assignment. When pieces
      overlap after the assignment, they are merged with [F.join
      ~controllable]: resilience join if the statement is A-controlled
      ([true]), approximation join otherwise ([false], default). *)

  val filter : ?controllable:bool -> ?domain:B.t ->  t -> expr typed -> t
  (** [filter ~controllable t exp] backward filter: prunes [t] and adds the
      condition [exp]. The join between the two branches of a conditional is
      not done here but by the iterator. *)
  val zero : env -> t
  val plus : t -> t -> t
  val defined : ?condition:expr typed -> t -> bool
  val refine : t -> B.t -> t

  (** {2 Temporal operators} Used by ATL and CTL; the termination analysis
      does not need them. *)

  val meet : kind -> t -> t -> t
  val dual_widen : t -> t -> t
  val partially_defined : ?condition:expr typed -> t -> bool
  val complement : t -> t
  val reset : ?mask:t -> t -> expr typed -> t
  val until : t -> t -> t -> t
  val mask : t -> t -> t

  (** {2 Under-approximating transformers} Called directly by CTL; [reset]
      also uses [ubwd_filter] internally. *)

  val ubwd_assign : ?domain:B.t -> ?controllable:bool ->  t -> expr typed * expr typed -> t
  val ubwd_filter :?controllable:bool -> ?domain:B.t -> t -> expr typed -> t

  (** {2 Conflict-driven analysis} Used by [Cda] ([compress] also by ATL and
      CTL). *)

  val learn : t -> t -> t
  val conflict : t -> B.t list
  val reinit : t -> t
  val compress : t -> t

  (** {2 Output} *)

  val print : Format.formatter -> t -> unit
  val output_json : var list -> t -> Yojson.Safe.t
  val print_graphviz_dot : Format.formatter -> t -> unit
end
