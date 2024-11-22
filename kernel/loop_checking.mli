(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Graphs representing strict orders *)

open Univ

type locality =
  | Global
  | Local

type t

val set_local : t -> t

val empty : t

val clear_constraints : t -> t

val check_invariants : required_canonical:(Level.t -> bool) -> t -> unit

exception AlreadyDeclared
val add : ?rank:int -> Level.t -> t -> t
(** All points must be pre-declared through this function before
    they can be mentioned in the others. NB: use a large [rank] to
    keep the node canonical *)

exception Undeclared of Level.t
val check_declared : t -> Level.Set.t -> (unit, Univ.Level.Set.t) result
(** @raise Undeclared if one of the points is not present in the graph. *)

type 'a check_function = t -> 'a -> 'a -> bool

val check_eq : Universe.t check_function
val check_leq : Universe.t check_function

type level_equivalences = (Level.t * (Level.t * int)) list

val enforce_eq : Universe.t -> Universe.t -> t -> (t * level_equivalences) option
val enforce_leq : Universe.t -> Universe.t -> t -> (t * level_equivalences) option
val enforce_lt : Universe.t -> Universe.t -> t -> (t * level_equivalences) option
val enforce_constraint : univ_constraint -> t -> (t * level_equivalences) option

exception InconsistentEquality

exception OccurCheck

(** [set idx u model] substitutes universe [u] for all occurrences of [idx] in model, resulting
in a set of constraints that no longer mentions [idx]. This is a stronger than [enforce_eq idx u],
as the [idx] universe is dropped from the constraints altogether. Returns a list of universes
that are also made equal by the new constraint and are also substituted by [u] in the resulting graph.
  @raise InconsistentEquality if setting [l = u] results in an unsatisfiable constraint
  @raise OccurCheck if the universe contains the level, up to equivalence in the graph *)
val set : Level.t -> Universe.t -> t -> t * level_equivalences

type extended_constraint_type =
  | ULe | ULt | UEq

type explanation = Universe.t * (extended_constraint_type * Universe.t) list

val get_explanation : univ_constraint -> t -> explanation
(** Assuming that the corresponding call to [enforce_*] returned [None], this
    will give a trace for the failure. *)

type 'a constraint_fold = univ_constraint -> 'a -> 'a

(** [constraints_of graph ?only_local fold acc = (levels, acc', equivs)]

  Computes the constraints modeled by the graph.
  If [only_local] is [true] (default is [false]), [levels] is the set of universes that were declared locally
  (since the last and only possible [set_local] call on the graph).
  The [Le] constraints are passed to a folding function starting with [acc] whose result is returned as [acc'].
  Finally [equivs] containts equivalence classes of level expressions, i.e. equality ([Eq]) constraints. *)
val constraints_of : t -> ?only_local:bool -> 'a constraint_fold -> 'a -> Level.Set.t * 'a * LevelExpr.Set.t list

val constraints_for : kept:Level.Set.t -> t -> 'a constraint_fold -> 'a -> 'a

val domain : t -> Level.Set.t

val choose : (Level.t -> bool) -> t -> Level.t -> Level.t option

type 'a simplification_result =
  | HasSubst of 'a * level_equivalences * Universe.t
  | NoBound
  | CannotSimplify

val minimize : Level.t -> t -> t simplification_result
val maximize : Level.t -> t -> t simplification_result

(* Hack for template-polymorphism. [remove_set_clauses u m] removes all [u -> Set+0] clauses from the model  *)
val remove_set_clauses : Level.t -> t -> t

(** {5 High-level representation} *)

type node =
| Alias of LevelExpr.t
| Node of (int * Universe.t) list (** Nodes [(k_i, u_i); ...] s.t. u + k_i <= u_i *)

type repr = node Level.Map.t

val repr : t -> repr

(* Print the model. Optionally print only the local universes and constraints. *)
val pr_model : ?local:bool -> t -> Pp.t

val valuation : t -> int Level.Map.t

(* Hook for more readable debug ouput, call it to set a function for printing levels (e.g. using their stable
  names rather than automatically generated unique identifiers).  *)

val set_debug_pr_level : (Level.t -> Pp.t) -> unit
