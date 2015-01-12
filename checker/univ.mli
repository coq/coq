(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Universes. *)

module Level :
sig
  type t
  (** Type of universe levels. A universe level is essentially a unique name
      that will be associated to constraints later on. *)

  val make : Names.DirPath.t -> int -> t
  (** Create a new universe level from a unique identifier and an associated
      module path. *)

  val equal : t -> t -> bool
end

type universe_level = Level.t
(** Alias name. *)

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

  val equal : t -> t -> bool
  (** Equality function on formal universes *)

  val make : Level.t -> t
  (** Create a universe representing the given level. *)

end

type universe = Universe.t

(** Alias name. *)

val pr_uni : universe -> Pp.std_ppcmds

(** The universes hierarchy: Type 0- = Prop <= Type 0 = Set <= Type 1 <= ...
   Typing of universes: Type 0-, Type 0 : Type 1; Type i : Type (i+1) if i>0 *)
val type0m_univ : universe
val type0_univ : universe
val type1_univ : universe

val is_type0_univ : universe -> bool
val is_type0m_univ : universe -> bool
val is_univ_variable : universe -> bool

val sup : universe -> universe -> universe
val super : universe -> universe

(** {6 Graphs of universes. } *)

type universes

type 'a check_function = universes -> 'a -> 'a -> bool
val check_leq : universe check_function
val check_eq : universe check_function

(** The initial graph of universes: Prop < Set *)
val initial_universes : universes

(** {6 Constraints. } *)

type constraint_type = Lt | Le | Eq
type univ_constraint = universe_level * constraint_type * universe_level

module Constraint : Set.S with type elt = univ_constraint

type constraints = Constraint.t

val empty_constraint : constraints

(** A value with universe constraints. *)
type 'a constrained = 'a * constraints

(** Enforcing constraints. *)

type 'a constraint_function = 'a -> 'a -> constraints -> constraints

val enforce_leq : universe constraint_function

(** {6 ... } *)
(** Merge of constraints in a universes graph.
  The function [merge_constraints] merges a set of constraints in a given
  universes graph. It raises the exception [UniverseInconsistency] if the
  constraints are not satisfiable. *)

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
type univ_inconsistency = constraint_type * universe * universe

exception UniverseInconsistency of univ_inconsistency

val merge_constraints : constraints -> universes -> universes

val check_constraints : constraints -> universes -> bool

(** {6 Support for universe polymorphism } *)

(** Polymorphic maps from universe levels to 'a *)
module LMap : Map.S with type key = universe_level

type 'a universe_map = 'a LMap.t

(** {6 Substitution} *)

type universe_subst_fn = universe_level -> universe
type universe_level_subst_fn = universe_level -> universe_level

(** A full substitution, might involve algebraic universes *)
type universe_subst = universe universe_map
type universe_level_subst = universe_level universe_map

val level_subst_of : universe_subst_fn -> universe_level_subst_fn

(** {6 Universe instances} *)

module Instance :
sig
  type t
  (** A universe instance represents a vector of argument universes
      to a polymorphic definition (constant, inductive or constructor). *)

  val empty : t
  val is_empty : t -> bool

  val equal : t -> t -> bool
  (** Equality (note: instances are hash-consed, this is O(1)) *)

  val subst_fn : universe_level_subst_fn -> t -> t
  (** Substitution by a level-to-level function. *)

  val subst : universe_level_subst -> t -> t
  (** Substitution by a level-to-level function. *)

  val pr : t -> Pp.std_ppcmds
  (** Pretty-printing, no comments *)

  val check_eq : t check_function
  (** Check equality of instances w.r.t. a universe graph *)
end

type universe_instance = Instance.t

type 'a puniverses = 'a * universe_instance

(** A vector of universe levels with universe constraints,
    representiong local universe variables and associated constraints *)

module UContext :
sig
  type t

  val empty : t

  val instance : t -> Instance.t
  val constraints : t -> constraints

end

module ContextSet :
  sig 
    type t
    val empty : t
    val constraints : t -> constraints
  end

type universe_context = UContext.t
type universe_context_set = ContextSet.t

val empty_level_subst : universe_level_subst
val is_empty_level_subst : universe_level_subst -> bool

(** Substitution of universes. *)
val subst_univs_level_level : universe_level_subst -> universe_level -> universe_level
val subst_univs_level_universe : universe_level_subst -> universe -> universe

(** Level to universe substitutions. *)

val is_empty_subst : universe_subst -> bool
val make_subst : universe_subst -> universe_subst_fn

val subst_univs_universe : universe_subst_fn -> universe -> universe

(** Substitution of instances *)
val subst_instance_instance : universe_instance -> universe_instance -> universe_instance
val subst_instance_universe : universe_instance -> universe -> universe
val subst_instance_constraints : universe_instance -> constraints -> constraints

(* val make_instance_subst : universe_instance -> universe_level_subst *)
(* val make_inverse_instance_subst : universe_instance -> universe_level_subst *)

(** Get the instantiated graph. *)
val instantiate_univ_context : universe_context -> universe_context
val instantiate_univ_constraints : universe_instance -> universe_context -> constraints

(** {6 Pretty-printing of universes. } *)

val pr_universes : universes -> Pp.std_ppcmds
