(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Qualified global universe level *)
module UGlobal :
sig

  type t

  val make : Names.DirPath.t -> string -> int -> t
  val repr : t -> Names.DirPath.t * string * int
  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int
  val to_string : t -> string

end

(** Universes. *)
module Level :
sig

  type t
  (** Type of universe levels. A universe level is essentially a unique name
      that will be associated to constraints later on. A level can be local to a
      definition or global. *)

  val set : t
  (** The Set universe level. *)

  val is_set : t -> bool
  (** Is the universe Set? *)

  val compare : t -> t -> int
  (** Comparison function *)

  val equal : t -> t -> bool
  (** Equality function *)

  val hash : t -> int

  val hcons : t -> t

  val make : UGlobal.t -> t

  val raw_pr : t -> Pp.t
  (** Pretty-printing.
      When possible you should use name-aware printing. *)

  val pr : t -> Pp.t
  [@@deprecated "(8.18) Use [UnivNames.pr_with_global_universes] instead if possible, otherwise [raw_pr]."]

  val to_string : t -> string
  (** Debug printing *)

  val var : int -> t

  val var_index : t -> int option

  val name : t -> UGlobal.t option

  module Set :
    sig
      include CSig.USetS with type elt = t

      val pr : (elt -> Pp.t) -> t -> Pp.t
      (** Pretty-printing *)
    end

  module Map :
  sig
    include CMap.UExtS with type key = t and module Set := Set

    val lunion : 'a t -> 'a t -> 'a t
    (** [lunion x y] favors the bindings in the first map. *)

    val diff : 'a t -> 'a t -> 'a t
    (** [diff x y] removes bindings from x that appear in y (whatever the value). *)

    val pr : (key -> Pp.t) -> ('a -> Pp.t) -> 'a t -> Pp.t
    (** Pretty-printing *)
  end

end

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

  val hcons : t -> t

  val make : Level.t -> t
  (** Create a universe representing the given level. *)

  val maken : Level.t -> int -> t
  (** Composition of [make] and iterated [super]. *)

  val pr : (Level.t -> Pp.t) -> t -> Pp.t
  (** Pretty-printing *)

  val raw_pr : t -> Pp.t

  val is_level : t -> bool
  (** Test if the universe is a level or an algebraic universe. *)

  val is_levels : t -> bool
  (** Test if the universe is a lub of levels or contains +n's. *)

  val level : t -> Level.t option
  (** Try to get a level out of a universe, returns [None] if it
      is an algebraic universe. *)

  val levels : ?init:Level.Set.t -> t -> Level.Set.t
  (** Get the levels inside the universe, forgetting about increments,
      and add them to [init] (default empty) *)

  val super : t -> t
  (** The universe strictly above *)

  val sup   : t -> t -> t
  (** The l.u.b. of 2 universes *)

  val type0 : t
  (** image of Set in the universes hierarchy *)

  val type1 : t
  (** the universe of the type of Prop/Set *)

  val is_type0 : t -> bool

  val exists : (Level.t * int -> bool) -> t -> bool
  val for_all : (Level.t * int -> bool) -> t -> bool

  val repr : t -> (Level.t * int) list
  val unrepr : (Level.t * int) list -> t

  module Set : CSet.ExtS with type elt  = t
  module Map : CMap.ExtS with type key = t and module Set := Set

end

(** [univ_level_mem l u] Is l is mentioned in u ? *)

val univ_level_mem : Level.t -> Universe.t -> bool

(** [univ_level_rem u v min] removes [u] from [v], resulting in [min]
    if [v] was exactly [u]. *)

val univ_level_rem : Level.t -> Universe.t -> Universe.t -> Universe.t

(** {6 Constraints. } *)

type constraint_type = AcyclicGraph.constraint_type = Lt | Le | Eq
type univ_constraint = Level.t * constraint_type * Level.t

module Constraints : sig
  include CSet.ExtS with type elt = univ_constraint

  val pr : (Level.t -> Pp.t) -> t -> Pp.t
end

(** A value with universe Constraints.t. *)
type 'a constrained = 'a * Constraints.t

(** Constrained *)
val constraints_of : 'a constrained -> Constraints.t

(** Enforcing Constraints.t. *)
type 'a constraint_function = 'a -> 'a -> Constraints.t -> Constraints.t

val enforce_eq_level : Level.t constraint_function
val enforce_leq_level : Level.t constraint_function

(** Universe contexts (as sets) *)

(** A set of universes with universe Constraints.t.
    We linearize the set to a list after typechecking.
    Beware, representation could change.
*)

module ContextSet :
sig
  type t = Level.Set.t constrained

  val empty : t
  val is_empty : t -> bool

  val singleton : Level.t -> t
  val of_set : Level.Set.t -> t

  val equal : t -> t -> bool
  val union : t -> t -> t

  val append : t -> t -> t
  (** Variant of {!union} which is more efficient when the left argument is
      much smaller than the right one. *)

  val diff : t -> t -> t
  val add_universe : Level.t -> t -> t
  val add_constraints : Constraints.t -> t -> t

  val constraints : t -> Constraints.t
  val levels : t -> Level.Set.t

  val size : t -> int
  (** The number of universes in the context *)

end

(** A value in a universe context set. *)
type 'a in_universe_context_set = 'a * ContextSet.t

(** {6 Substitution} *)

type universe_level_subst = Level.t Level.Map.t

val empty_level_subst : universe_level_subst
val is_empty_level_subst : universe_level_subst -> bool

(** Substitution of universes. *)
val subst_univs_level_level : universe_level_subst -> Level.t -> Level.t
val subst_univs_level_universe : universe_level_subst -> Universe.t -> Universe.t
val subst_univs_level_constraints : universe_level_subst -> Constraints.t -> Constraints.t

(** {6 Pretty-printing of universes. } *)

val pr_constraint_type : constraint_type -> Pp.t
val pr_universe_context_set : (Level.t -> Pp.t) -> ContextSet.t -> Pp.t

val pr_universe_level_subst : (Level.t -> Pp.t) -> universe_level_subst -> Pp.t

(** {6 Hash-consing } *)

val hcons_univ : Universe.t -> Universe.t
val hcons_constraints : Constraints.t -> Constraints.t
val hcons_universe_set : Level.Set.t -> Level.Set.t
val hcons_universe_context_set : ContextSet.t -> ContextSet.t
