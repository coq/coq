(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Universes. *)
module Public : sig

module Level :
sig
  type t
  (** Type of universe levels. A universe level is essentially a unique name
      that will be associated to constraints later on. *)

  val set : t
  val prop : t
  (** The set and prop universe levels. *)

  val is_small : t -> bool
  (** Is the universe set or prop? *)

  val is_prop : t -> bool
  val is_set : t -> bool
  (** Is it specifically Prop or Set *)

  val compare : t -> t -> int
  (** Comparison function *)

  val equal : t -> t -> bool
  (** Equality function *)

  val hash : t -> int

  val make : Names.DirPath.t -> int -> t
  (** Create a new universe level from a unique identifier and an associated
      module path. *)

  val pr : t -> Pp.t
  (** Pretty-printing *)

  val to_string : t -> string
  (** Debug printing *)

  val var : int -> t

  val var_index : t -> int option
end

type universe_level = Level.t
[@@ocaml.deprecated "Use Level.t"]

(** Sets of universe levels *)
module LSet :
sig
  include CSig.SetS with type elt = Level.t

  val pr : (Level.t -> Pp.t) -> t -> Pp.t
  (** Pretty-printing *)
end

type universe_set = LSet.t
[@@ocaml.deprecated "Use LSet.t"]

module Universe :
sig
  type t
  (** Type of universes. A universe is defined as a set of level expressions.
      A level expression is built from levels and successors of level expressions, i.e.:
      le ::= l + n, n \in N.

      A universe is said atomic if it consists of a single level expression with
      no increment, and algebraic otherwise (think the least upper bound of a set of
      level expressions).
  *)

  val compare : t -> t -> int
  (** Comparison function *)

  val equal : t -> t -> bool
  (** Equality function on formal universes *)

  val hash : t -> int
  (** Hash function *)

  val make : Level.t -> t
  (** Create a universe representing the given level. *)

  val pr : t -> Pp.t
  (** Pretty-printing *)

  val pr_with : (Level.t -> Pp.t) -> t -> Pp.t

  val is_level : t -> bool
  (** Test if the universe is a level or an algebraic universe. *)

  val is_levels : t -> bool
  (** Test if the universe is a lub of levels or contains +n's. *)

  val level : t -> Level.t option
  (** Try to get a level out of a universe, returns [None] if it
      is an algebraic universe. *)

  val levels : t -> LSet.t
  (** Get the levels inside the universe, forgetting about increments *)

  val super : t -> t
  (** The universe strictly above *)

  val sup   : t -> t -> t
  (** The l.u.b. of 2 universes *)

  val type0m : t
  (** image of Prop in the universes hierarchy *)

  val type0 : t
  (** image of Set in the universes hierarchy *)

  val type1 : t
  (** the universe of the type of Prop/Set *)

  val exists : (Level.t * int -> bool) -> t -> bool
  val for_all : (Level.t * int -> bool) -> t -> bool
end

type universe = Universe.t
[@@ocaml.deprecated "Use Universe.t"]

(** Alias name. *)

val pr_uni : Universe.t -> Pp.t

(** The universes hierarchy: Type 0- = Prop <= Type 0 = Set <= Type 1 <= ...
   Typing of universes: Type 0-, Type 0 : Type 1; Type i : Type (i+1) if i>0 *)
val type0m_univ : Universe.t
val type0_univ : Universe.t
val type1_univ : Universe.t

val is_type0_univ : Universe.t -> bool
val is_type0m_univ : Universe.t -> bool
val is_univ_variable : Universe.t -> bool
val is_small_univ : Universe.t -> bool

val sup : Universe.t -> Universe.t -> Universe.t
val super : Universe.t -> Universe.t

val universe_level : Universe.t -> Level.t option

(** [univ_level_mem l u] Is l is mentionned in u ? *)

val univ_level_mem : Level.t -> Universe.t -> bool

(** [univ_level_rem u v min] removes [u] from [v], resulting in [min]
    if [v] was exactly [u]. *)

val univ_level_rem : Level.t -> Universe.t -> Universe.t -> Universe.t

(** {6 Constraints. } *)

type constraint_type = Lt | Le | Eq
type univ_constraint = Level.t * constraint_type * Level.t

module Constraint : sig
 include Set.S with type elt = univ_constraint
end

type constraints = Constraint.t

val empty_constraint : constraints
val union_constraint : constraints -> constraints -> constraints
val eq_constraint : constraints -> constraints -> bool

(** A value with universe constraints. *)
type 'a constrained = 'a * constraints

(** Constrained *)
val constraints_of : 'a constrained -> constraints

(** Enforcing constraints. *)

type 'a constraint_function = 'a -> 'a -> constraints -> constraints

val enforce_eq : Universe.t constraint_function
val enforce_leq : Universe.t constraint_function
val enforce_eq_level : Level.t constraint_function
val enforce_leq_level : Level.t constraint_function

(** Type explanation is used to decorate error messages to provide
  useful explanation why a given constraint is rejected. It is composed
  of a path of universes and relation kinds [(r1,u1);..;(rn,un)] means
   .. <(r1) u1 <(r2) ... <(rn) un (where <(ri) is the relation symbol
  denoted by ri, currently only < and <=). The lowest end of the chain
  is supposed known (see UniverseInconsistency exn). The upper end may
  differ from the second univ of UniverseInconsistency because all
  universes in the path are canonical. Note that each step does not
  necessarily correspond to an actual constraint, but reflect how the
  system stores the graph and may result from combination of several
  constraints...
*)
type explanation = (constraint_type * Universe.t) list
type univ_inconsistency = constraint_type * Universe.t * Universe.t * explanation option

exception UniverseInconsistency of univ_inconsistency

(** {6 Support for universe polymorphism } *)

(** Polymorphic maps from universe levels to 'a *)
module LMap :
sig
  include CMap.ExtS with type key = Level.t and module Set := LSet

  val union : 'a t -> 'a t -> 'a t
  (** [union x y] favors the bindings in the first map. *)

  val diff : 'a t -> 'a t -> 'a t
  (** [diff x y] removes bindings from x that appear in y (whatever the value). *)

  val subst_union : 'a option t -> 'a option t -> 'a option t
  (** [subst_union x y] favors the bindings of the first map that are [Some],
      otherwise takes y's bindings. *)

  val pr : ('a -> Pp.t) -> 'a t -> Pp.t
  (** Pretty-printing *)
end

type 'a universe_map = 'a LMap.t

(** {6 Substitution} *)

type universe_subst_fn = Level.t -> Universe.t
type universe_level_subst_fn = Level.t -> Level.t

(** A full substitution, might involve algebraic universes *)
type universe_subst = Universe.t universe_map
type universe_level_subst = Level.t universe_map

val level_subst_of : universe_subst_fn -> universe_level_subst_fn

(** {6 Universe instances} *)

module Instance :
sig
  type t
  (** A universe instance represents a vector of argument universes
      to a polymorphic definition (constant, inductive or constructor). *)

  val empty : t
  val is_empty : t -> bool

  val of_array : Level.t array -> t
  val to_array : t -> Level.t array

  val append : t -> t -> t
  (** To concatenate two instances, used for discharge *)

  val equal : t -> t -> bool
  (** Equality *)

  val length : t -> int
  (** Instance length *)

  val hcons : t -> t
  (** Hash-consing. *)

  val hash : t -> int
  (** Hash value *)

  val share : t -> t * int
  (** Simultaneous hash-consing and hash-value computation *)

  val subst_fn : universe_level_subst_fn -> t -> t
  (** Substitution by a level-to-level function. *)

  val pr : (Level.t -> Pp.t) -> t -> Pp.t
  (** Pretty-printing, no comments *)

  val levels : t -> LSet.t
  (** The set of levels in the instance *)

end

type universe_instance = Instance.t
[@@ocaml.deprecated "Use Instance.t"]

val enforce_eq_instances : Instance.t constraint_function

type 'a puniverses = 'a * Instance.t
val out_punivs : 'a puniverses -> 'a
val in_punivs : 'a -> 'a puniverses

val eq_puniverses : ('a -> 'a -> bool) -> 'a puniverses -> 'a puniverses -> bool

(** A vector of universe levels with universe constraints,
    representiong local universe variables and associated constraints *)

module UContext :
sig
  type t

  val make : Instance.t constrained -> t

  val empty : t
  val is_empty : t -> bool

  val instance : t -> Instance.t
  val constraints : t -> constraints

  val dest : t -> Instance.t * constraints

  (** Keeps the order of the instances *)
  val union : t -> t -> t

  (* the number of universes in the context *)
  val size : t -> int

end

type universe_context = UContext.t
[@@ocaml.deprecated "Use UContext.t"]

module AUContext :
sig
  type t

  val repr : t -> UContext.t
  (** [repr ctx] is [(Var(0), ... Var(n-1) |= cstr] where [n] is the length of
      the context and [cstr] the abstracted constraints. *)

  val empty : t
  val is_empty : t -> bool

  (** Don't use. *)
  val instance : t -> Instance.t

  val size : t -> int

  (** Keeps the order of the instances *)
  val union : t -> t -> t

  val instantiate : Instance.t -> t -> Constraint.t
  (** Generate the set of instantiated constraints **)

end

type abstract_universe_context = AUContext.t
[@@ocaml.deprecated "Use AUContext.t"]

(** Universe info for inductive types: A context of universe levels
    with universe constraints, representing local universe variables
    and constraints, together with a context of universe levels with
    universe constraints, representing conditions for subtyping used
    for inductive types.

    This data structure maintains the invariant that the context for
    subtyping constraints is exactly twice as big as the context for
    universe constraints. *)
module CumulativityInfo :
sig
  type t

  val make : UContext.t * UContext.t -> t

  val empty : t
  val is_empty : t -> bool

  val univ_context : t -> UContext.t
  val subtyp_context : t -> UContext.t

  (** This function takes a universe context representing constraints
      of an inductive and a Instance.t of fresh universe names for the
      subtyping (with the same length as the context in the given
      universe context) and produces a UInfoInd.t that with the
      trivial subtyping relation. *)
  val from_universe_context : UContext.t -> Instance.t -> t

  val subtyping_susbst : t -> universe_level_subst

end

type cumulativity_info = CumulativityInfo.t
[@@ocaml.deprecated "Use CumulativityInfo.t"]

module ACumulativityInfo :
sig
  type t

  val univ_context : t -> AUContext.t
  val subtyp_context : t -> AUContext.t
end

type abstract_cumulativity_info = ACumulativityInfo.t
[@@ocaml.deprecated "Use ACumulativityInfo.t"]

(** Universe contexts (as sets) *)

module ContextSet :
sig
  type t = LSet.t constrained

  val empty : t
  val is_empty : t -> bool

  val singleton : Level.t -> t
  val of_instance : Instance.t -> t
  val of_set : LSet.t -> t

  val equal : t -> t -> bool
  val union : t -> t -> t

  val append : t -> t -> t
  (** Variant of {!union} which is more efficient when the left argument is
      much smaller than the right one. *)

  val diff : t -> t -> t
  val add_universe : Level.t -> t -> t
  val add_constraints : constraints -> t -> t
  val add_instance : Instance.t -> t -> t

  (** Arbitrary choice of linear order of the variables *)
  val sort_levels : Level.t array -> Level.t array
  val to_context : t -> UContext.t
  val of_context : UContext.t -> t

  val constraints : t -> constraints
  val levels : t -> LSet.t
end

(** A set of universes with universe constraints.
    We linearize the set to a list after typechecking.
    Beware, representation could change.
*)
type universe_context_set = ContextSet.t
[@@ocaml.deprecated "Use ContextSet.t"]

(** A value in a universe context (resp. context set). *)
type 'a in_universe_context = 'a * UContext.t
type 'a in_universe_context_set = 'a * ContextSet.t

val empty_level_subst : universe_level_subst
val is_empty_level_subst : universe_level_subst -> bool

(** Substitution of universes. *)
val subst_univs_level_level : universe_level_subst -> Level.t -> Level.t
val subst_univs_level_universe : universe_level_subst -> Universe.t -> Universe.t
val subst_univs_level_constraints : universe_level_subst -> constraints -> constraints
val subst_univs_level_abstract_universe_context :
  universe_level_subst -> AUContext.t -> AUContext.t
val subst_univs_level_instance : universe_level_subst -> Instance.t -> Instance.t

(** Level to universe substitutions. *)

val empty_subst : universe_subst
val is_empty_subst : universe_subst -> bool
val make_subst : universe_subst -> universe_subst_fn

val subst_univs_universe : universe_subst_fn -> Universe.t -> Universe.t
val subst_univs_constraints : universe_subst_fn -> constraints -> constraints

(** Substitution of instances *)
val subst_instance_instance : Instance.t -> Instance.t -> Instance.t
val subst_instance_universe : Instance.t -> Universe.t -> Universe.t

val make_instance_subst : Instance.t -> universe_level_subst
val make_inverse_instance_subst : Instance.t -> universe_level_subst

val abstract_universes : UContext.t -> universe_level_subst * AUContext.t

val abstract_cumulativity_info : CumulativityInfo.t -> universe_level_subst * ACumulativityInfo.t

val make_abstract_instance : AUContext.t -> Instance.t

(** {6 Pretty-printing of universes. } *)

val pr_constraint_type : constraint_type -> Pp.t
val pr_constraints : (Level.t -> Pp.t) -> constraints -> Pp.t
val pr_universe_context : (Level.t -> Pp.t) -> UContext.t -> Pp.t
val pr_cumulativity_info : (Level.t -> Pp.t) -> CumulativityInfo.t -> Pp.t
val pr_abstract_universe_context : (Level.t -> Pp.t) -> AUContext.t -> Pp.t
val pr_abstract_cumulativity_info : (Level.t -> Pp.t) -> ACumulativityInfo.t -> Pp.t
val pr_universe_context_set : (Level.t -> Pp.t) -> ContextSet.t -> Pp.t
val explain_universe_inconsistency : (Level.t -> Pp.t) ->
  univ_inconsistency -> Pp.t

val pr_universe_level_subst : universe_level_subst -> Pp.t
val pr_universe_subst : universe_subst -> Pp.t

(** {6 Hash-consing } *)

val hcons_univ : Universe.t -> Universe.t
val hcons_constraints : constraints -> constraints
val hcons_universe_set : LSet.t -> LSet.t
val hcons_universe_context : UContext.t -> UContext.t
val hcons_abstract_universe_context : AUContext.t -> AUContext.t
val hcons_universe_context_set : ContextSet.t -> ContextSet.t
val hcons_cumulativity_info : CumulativityInfo.t -> CumulativityInfo.t
val hcons_abstract_cumulativity_info : ACumulativityInfo.t -> ACumulativityInfo.t

(******)

(* deprecated: use qualified names instead *)
val compare_levels : Level.t -> Level.t -> int
[@@ocaml.deprecated "Use Level.compare"]

val eq_levels : Level.t -> Level.t -> bool
[@@ocaml.deprecated "Use Level.equal"]

(** deprecated: Equality of formal universe expressions. *)
val equal_universes : Universe.t -> Universe.t -> bool
[@@ocaml.deprecated "Use Universe.equal"]

(** Universes of constraints *)
val universes_of_constraints : constraints -> LSet.t
[@@ocaml.deprecated "Use Constraint.universes_of"]

end

include module type of Public

(* Nothing is internal for now, but likely some stuff should be added here *)
module Internal : sig
end
