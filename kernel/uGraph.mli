(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ

(** {6 Graphs of universes. } *)
type t
type universes = t
[@@ocaml.deprecated "Use UGraph.t"]

type 'a check_function = t -> 'a -> 'a -> bool

val check_leq : Universe.t check_function
val check_eq : Universe.t check_function
val check_eq_level : Level.t check_function

(** The initial graph of universes: Prop < Set *)
val initial_universes : t

(** Check if we are in the initial case *)
val is_initial_universes : t -> bool

(** Check equality of instances w.r.t. a universe graph *)
val check_eq_instances : Instance.t check_function

(** {6 ... } *)
(** Merge of constraints in a universes graph.
  The function [merge_constraints] merges a set of constraints in a given
  universes graph. It raises the exception [UniverseInconsistency] if the
  constraints are not satisfiable. *)

val enforce_constraint : univ_constraint -> t -> t
val merge_constraints : Constraint.t -> t -> t

val check_constraint  : t -> univ_constraint -> bool
val check_constraints : Constraint.t -> t -> bool

(** Picks an arbitrary set of constraints sufficient to ensure [u <= v]. *)
val enforce_leq_alg : Universe.t -> Universe.t -> t -> Constraint.t * t

(** Adds a universe to the graph, ensuring it is >= or > Set.
   @raise AlreadyDeclared if the level is already declared in the graph. *)

exception AlreadyDeclared

val add_universe : Level.t -> bool -> t -> t

(** Add a universe without (Prop,Set) <= u *)
val add_universe_unconstrained : Level.t -> t -> t

(** Check that the universe levels are declared. Otherwise
    @raise UndeclaredLevel l for the first undeclared level found. *)
exception UndeclaredLevel of Univ.Level.t

val check_declared_universes : t -> Univ.LSet.t -> unit

(** {6 Pretty-printing of universes. } *)

val pr_universes : (Level.t -> Pp.t) -> t -> Pp.t

(** The empty graph of universes *)
val empty_universes : t

val sort_universes : t -> t

(** [constraints_of_universes g] returns [csts] and [partition] where
   [csts] are the non-Eq constraints and [partition] is the partition
   of the universes into equivalence classes. *)
val constraints_of_universes : t -> Constraint.t * LSet.t list

(** [constraints_for ~kept g] returns the constraints about the
   universes [kept] in [g] up to transitivity.

    eg if [g] is [a <= b <= c] then [constraints_for ~kept:{a, c} g] is [a <= c]. *)
val constraints_for : kept:LSet.t -> t -> Constraint.t

val check_subtype : AUContext.t check_function
(** [check_subtype univ ctx1 ctx2] checks whether [ctx2] is an instance of
    [ctx1]. *)

(** {6 Dumping to a file } *)

val dump_universes :
  (constraint_type -> string -> string -> unit) -> t -> unit

(** {6 Debugging} *)
val check_universes_invariants : t -> unit
