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

(** When [type_in_type], functions adding level constraints do not fail and
   may instead ignore inconsistent constraints.

    Checking functions such as [check_leq] always return [true].
*)
val type_in_type : t -> bool

type 'a check_function = t -> 'a -> 'a -> bool

val check_leq : Universe.t check_function
val check_eq : Universe.t check_function

(** The initial graph of universes: Prop < Set *)
val initial_universes : t

type locality = Loop_checking.locality =
  | Global
  | Local

(** In the resulting graph, additions of universes and constraints are considered local,
   and they can be retrieved using the only_local/local options of accessort functions below. *)
val set_local : t -> t

(** Check equality of instances w.r.t. a universe graph *)
val check_eq_instances : (Sorts.Quality.t -> Sorts.Quality.t -> bool) -> t -> Instance.t -> Instance.t -> bool

(** {6 ... } *)
(** Merge of constraints in a universes graph.
  The function [merge_constraints] merges a set of constraints in a given
  universes graph. It raises the exception [UniverseInconsistency] if the
  constraints are not satisfiable. *)

type path_explanation

type explanation =
  | Path of path_explanation
  | Other of Pp.t

type univ_inconsistency = Sorts.printer option * (UnivConstraint.kind * Sorts.t * Sorts.t * explanation option)

exception UniverseInconsistency of univ_inconsistency

type level_equivalences = (Level.t * (Level.t * int)) list

val enforce_constraint : UnivConstraint.t -> t -> t * level_equivalences

val merge_constraints : UnivConstraints.t -> t -> t * level_equivalences

val check_constraint  : t -> UnivConstraint.t -> bool
val check_constraints : UnivConstraints.t -> t -> bool

val check_eq_sort : (Sorts.Quality.t -> Sorts.Quality.t -> bool) -> t -> Sorts.t -> Sorts.t -> bool
(** Checks whether (i) the first quality is equal to the second and (ii)
    that the universe of the first one is equal to the universe of the second one. *)

val check_leq_sort : (Sorts.Quality.t -> Sorts.Quality.t -> bool) -> t -> Sorts.t -> Sorts.t -> bool
(** Checks whether (i) the second quality eliminates into the first and (ii)
    that the universe of the first one is below the universe of the second one. *)

val normalize : t -> Level.t -> Universe.t option

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

exception AlreadyDeclared
val add_universe : Level.t -> strict:bool -> rigid:bool -> t -> t
(** Adds a universe to the graph, ensuring it is >= or > (if [strict = true]) Set.
   A [rigid] level is kept canonical when it is made equal to a non-rigid expression.
   @raise AlreadyDeclared if the level is already declared in the graph. *)


(** Check that the universe levels are declared. *)
val check_declared_universes : t -> Univ.Level.Set.t -> (unit, Univ.Level.Set.t) result

val is_declared : t -> Level.t -> bool

(** The empty graph of universes *)
val empty_universes : t

(** [constraints_of_universes only_local g] returns [csts] and [partition] where
   [csts] are the non-Eq constraints and [partition] is the partition
   of the universes into equivalence classes.
   The [only_local] option only returns the constraints added since [set_local] was performed
   on the graph. *)
val constraints_of_universes : ?only_local:bool -> t ->
   Level.Set.t * UnivConstraints.t * (locality * Universe.t) Level.Map.t

(** [constraints_for ~kept g] returns the constraints about the
   universes [kept] in [g] up to transitivity.
   e.g. if [g] is [a <= b <= c] then [constraints_for ~kept:{a, c} g] is [a <= c]. *)
val constraints_for : kept:Level.Set.t -> t -> UnivConstraints.t

(** [remove l g] returns the graph [g] where the [l] universes have been removed,
   keeping the existing constraints between kept universes.
   e.g. if [g] is [a <= b <= c] then [remove {b} g] is [a <= c]. *)
val remove : Level.Set.t -> t -> t

val minimize : Level.t -> t -> t Loop_checking.simplification_result
val maximize : Level.t -> t -> t Loop_checking.simplification_result

(* Hack for template polymorphism *)
val remove_set_clauses : Level.t -> t -> t

(* Print the model. Optionally print only the local universes and constraints. *)
val pr_model : ?local:bool -> t -> Pp.t

val domain : t -> Level.Set.t
(** Known universes. *)

val variables : local:bool -> with_subst:bool -> t -> Level.Set.t
(** Computes the set of registered variables, optionally restricted to local ones, and
  optionally including the substituted variables. *)

val subst : ?local:bool -> t -> (locality * Universe.t) Level.Map.t
(** Substitution from (local) levels to universes.
   N.B.: slighty expensive to compute, better use [normalize] below. *)

val switch_locality : Level.t -> t -> t
(** Turn a local universe into a non-local one and conversely. *)

(** {6 Dumping} *)

type node =
| Alias of Universe.t
| Node of (int * Universe.t) list (** Nodes [(k_i, u_i); ...] s.t. u + k_i <= u_i *)

val repr : ?local:bool -> t -> node Level.Map.t

(** {6 Pretty-printing of universes. } *)

val pr_universes : (Level.t -> Pp.t) -> node Level.Map.t -> Pp.t

val explain_universe_inconsistency : Sorts.printer -> univ_inconsistency -> Pp.t

val pr : ?local:bool -> (Level.t -> Pp.t) -> t -> Pp.t
(** [pr_universes] of [repr] *)

(** {6 Debugging} *)
val check_universes_invariants : t -> unit

module Internal : sig
  (** Makes the qvars treated as above prop.
      Do not use outside kernel inductive typechecking. *)
  val add_template_qvars : Sorts.QVar.Set.t -> t -> t

  val is_above_prop : t -> Sorts.QVar.t -> bool
end
