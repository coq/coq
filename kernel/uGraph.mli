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

(** Adds a universe to the graph, ensuring it is >= or > Set.
   @raise AlreadyDeclared if the level is already declared in the graph. *)

exception AlreadyDeclared

val add_universe : Level.t -> bool -> t -> t

(** {6 Pretty-printing of universes. } *)

val pr_universes : (Level.t -> Pp.t) -> t -> Pp.t

(** The empty graph of universes *)
val empty_universes : t
[@@ocaml.deprecated "Use UGraph.initial_universes"]

val sort_universes : t -> t

val constraints_of_universes : t -> Constraint.t

val check_subtype : AUContext.t check_function
(** [check_subtype univ ctx1 ctx2] checks whether [ctx2] is an instance of
    [ctx1]. *)

(** {6 Dumping to a file } *)

val dump_universes :
  (constraint_type -> string -> string -> unit) -> t -> unit

(** {6 Debugging} *)
val check_universes_invariants : t -> unit
