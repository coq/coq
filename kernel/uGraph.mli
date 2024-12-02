(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ
open UVars

(** {6 Graphs of universes. } *)
type t

val set_type_in_type : bool -> t -> t

(** When [type_in_type], functions adding constraints do not fail and
   may instead ignore inconsistent constraints.

    Checking functions such as [check_leq] always return [true].
*)
val type_in_type : t -> bool

type 'a check_function = t -> 'a -> 'a -> bool

val check_leq : Universe.t check_function
val check_eq : Universe.t check_function

(** The initial graph of universes: Prop < Set *)
val initial_universes : t

(** In the resulting graph, additions of universes and constraints are considered local,
   and they can be retrieved using the only_local option of constraints. *)
val set_local : t -> t

(** Initial universes, but keeping options such as type in type from the argument. *)
val clear_constraints : t -> t

(** Check equality of instances w.r.t. a universe graph *)
val check_eq_instances : Instance.t check_function

(** {6 ... } *)
(** Merge of constraints in a universes graph.
  The function [merge_constraints] merges a set of constraints in a given
  universes graph. It raises the exception [UniverseInconsistency] if the
  constraints are not satisfiable. *)

type path_explanation

type explanation =
  | Path of path_explanation
  | Other of Pp.t

type univ_variable_printers = (Sorts.QVar.t -> Pp.t) * (Level.t -> Pp.t)
type univ_inconsistency = univ_variable_printers option * (constraint_type * Sorts.t * Sorts.t * explanation option)

exception UniverseInconsistency of univ_inconsistency

type level_equivalences = (Level.t * (Level.t * int)) list

val enforce_constraint : univ_constraint -> t -> t * level_equivalences

val merge_constraints : Constraints.t -> t -> t * level_equivalences

val check_constraint  : t -> univ_constraint -> bool
val check_constraints : Constraints.t -> t -> bool
val check_eq_sort : t -> Sorts.t  -> Sorts.t -> bool
val check_leq_sort : t -> Sorts.t -> Sorts.t -> bool

exception InconsistentEquality
exception OccurCheck
(** Sets a universe level equal to a universe in the graph.
   Stronger than enforcing an equality as the level disappears from the
   graph in case of success. Returns a new graph + a list of universe levels
   that are made equal due to the constraint and also disappear from the graph as a result.
   @raise InconsistentEquality if the equality cannot be enforced.
   @raise OccurCheck if the level appears in the universe, up to equivalence in the graph
   *)
val set : Level.t -> Universe.t -> t -> t * level_equivalences

(** Adds a universe to the graph, ensuring it is >= or > Set.
   @raise AlreadyDeclared if the level is already declared in the graph. *)

exception AlreadyDeclared

module Bound :
sig
  type t = Prop | Set
  (** The [Prop] bound is only used for template polymorphic inductive types. *)
end

val add_universe : Level.t -> lbound:Bound.t -> strict:bool -> t -> t

(** Check that the universe levels are declared. *)
val check_declared_universes : t -> Univ.Level.Set.t -> (unit, Univ.Level.Set.t) result

(** The empty graph of universes *)
val empty_universes : t

(** [constraints_of_universes only_local g] returns [csts] and [partition] where
   [csts] are the non-Eq constraints and [partition] is the partition
   of the universes into equivalence classes mapping a level to its equivalent
   level expressions (i.e. l = l' + k).
   The [only_local] option only returns the constraints added since [set_local] was performed
   on the graph. *)
val constraints_of_universes : ?only_local:bool -> t -> Level.Set.t * Constraints.t * LevelExpr.Set.t list

val choose : (Level.t -> bool) -> t -> Level.t -> Level.t option
(** [choose p g u] picks a universe verifying [p] and equal
   to [u] in [g]. *)

(** [constraints_for ~kept g] returns the constraints about the
   universes [kept] in [g] up to transitivity.
   e.g. if [g] is [a <= b <= c] then [constraints_for ~kept:{a, c} g] is [a <= c]. *)
val constraints_for : kept:Level.Set.t -> t -> Constraints.t

val minimize : Level.t -> t -> t Loop_checking.simplification_result
val maximize : Level.t -> t -> t Loop_checking.simplification_result

(* Hack for template polymorphism *)
val remove_set_clauses : Level.t -> t -> t

(* Print the model. Optionally print only the local universes and constraints. *)
val pr_model : ?local:bool -> t -> Pp.t

val domain : t -> Level.Set.t
(** Known universes *)

val check_subtype : AbstractContext.t check_function
(** [check_subtype univ ctx1 ctx2] checks whether [ctx2] is an instance of
    [ctx1]. *)

(** {6 Dumping} *)

type node =
| Alias of LevelExpr.t
| Node of (int * Universe.t) list (** Nodes [(k_i, u_i); ...] s.t. u + k_i <= u_i *)

val repr : t -> node Level.Map.t

(** {6 Pretty-printing of universes. } *)

val pr_universes : (Level.t -> Pp.t) -> node Level.Map.t -> Pp.t

val explain_universe_inconsistency : (Sorts.QVar.t -> Pp.t) -> (Level.t -> Pp.t) ->
  univ_inconsistency -> Pp.t

(** {6 Debugging} *)
val check_universes_invariants : t -> unit
