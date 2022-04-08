(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ

(** {6 Graphs of universes. } *)
type t

val set_cumulative_sprop : bool -> t -> t
(** Makes the system incomplete. *)

val set_type_in_type : bool -> t -> t

(** When [type_in_type], functions adding constraints do not fail and
   may instead ignore inconsistent constraints.

    Checking functions such as [check_leq] always return [true].
*)
val type_in_type : t -> bool
val cumulative_sprop : t -> bool

type 'a check_function = t -> 'a -> 'a -> bool

val check_leq : Universe.t check_function
val check_eq : Universe.t check_function
val check_eq_level : Level.t check_function

(** The initial graph of universes: Prop < Set *)
val initial_universes : t

(** Initial universes, but keeping options such as type in type from the argument. *)
val initial_universes_with : t -> t

(** Check equality of instances w.r.t. a universe graph *)
val check_eq_instances : Instance.t check_function

(** {6 ... } *)
(** Merge of constraints in a universes graph.
  The function [merge_constraints] merges a set of constraints in a given
  universes graph. It raises the exception [UniverseInconsistency] if the
  constraints are not satisfiable. *)

type univ_inconsistency = constraint_type * Sorts.t * Sorts.t * explanation Lazy.t option

exception UniverseInconsistency of univ_inconsistency

val enforce_constraint : univ_constraint -> t -> t

val merge_constraints : Constraints.t -> t -> t

val check_constraint  : t -> univ_constraint -> bool
val check_constraints : Constraints.t -> t -> bool
val check_eq_sort : t -> Sorts.t  -> Sorts.t -> bool
val check_leq_sort : t -> Sorts.t -> Sorts.t -> bool

val enforce_leq_alg : Univ.Universe.t -> Univ.Universe.t -> t -> Univ.Constraints.t * t

(** Adds a universe to the graph, ensuring it is >= or > Set.
   @raise AlreadyDeclared if the level is already declared in the graph. *)

exception AlreadyDeclared

module Bound :
sig
  type t = Prop | Set
  (** The [Prop] bound is only used for template polymorphic inductive types. *)
end

val add_universe : Level.t -> lbound:Bound.t -> strict:bool -> t -> t

(** Check that the universe levels are declared. Otherwise
    @raise UndeclaredLevel l for the first undeclared level found. *)
exception UndeclaredLevel of Univ.Level.t

val check_declared_universes : t -> Univ.Level.Set.t -> unit

(** The empty graph of universes *)
val empty_universes : t

(** [constraints_of_universes g] returns [csts] and [partition] where
   [csts] are the non-Eq constraints and [partition] is the partition
   of the universes into equivalence classes. *)
val constraints_of_universes : t -> Constraints.t * Level.Set.t list

val choose : (Level.t -> bool) -> t -> Level.t -> Level.t option
(** [choose p g u] picks a universe verifying [p] and equal
   to [u] in [g]. *)

(** [constraints_for ~kept g] returns the constraints about the
   universes [kept] in [g] up to transitivity.

    eg if [g] is [a <= b <= c] then [constraints_for ~kept:{a, c} g] is [a <= c]. *)
val constraints_for : kept:Level.Set.t -> t -> Constraints.t

val domain : t -> Level.Set.t
(** Known universes *)

val check_subtype : AbstractContext.t check_function
(** [check_subtype univ ctx1 ctx2] checks whether [ctx2] is an instance of
    [ctx1]. *)

(** {6 Dumping} *)

type node =
| Alias of Level.t
| Node of bool Level.Map.t (** Nodes v s.t. u < v (true) or u <= v (false) *)

val repr : t -> node Level.Map.t

(** {6 Pretty-printing of universes. } *)

val pr_universes : (Level.t -> Pp.t) -> node Level.Map.t -> Pp.t

val explain_universe_inconsistency : (Level.t -> Pp.t) ->
  univ_inconsistency -> Pp.t

(** {6 Debugging} *)
val check_universes_invariants : t -> unit
