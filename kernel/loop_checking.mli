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

val check_invariants : required_canonical:(Level.t -> bool) -> t -> unit

exception AlreadyDeclared
val add : ?rigid:bool -> Level.t -> t -> t
(** All points must be pre-declared through this function before
    they can be mentioned in the others. NB: use [rigid] to
    prefer to keep the node canonical if it is made equal to another *)

exception Undeclared of Level.t
(** This exception can be raised by any of the functions below taking a Level.t/Universe.t input
  that contains an undeclared level. *)

val is_declared : t -> Level.t -> bool
(** Check if a level was previously delared in the graph *)

val check_declared : t -> Level.Set.t -> (unit, Univ.Level.Set.t) result
(** Check if a set of levels are declared and return the undeclared ones on error. *)

type 'a check_function = t -> 'a -> 'a -> bool

val check_eq : Universe.t check_function
val check_leq : Universe.t check_function

type level_equivalences = (Level.t * (Level.t * int)) list

val enforce_eq : Universe.t -> Universe.t -> t -> (t * level_equivalences) option
val enforce_leq : Universe.t -> Universe.t -> t -> (t * level_equivalences) option
val enforce_lt : Universe.t -> Universe.t -> t -> (t * level_equivalences) option
val enforce_constraint : UnivConstraint.t -> t -> (t * level_equivalences) option

(** Normalize a level to its canonical representative.
  This uses the internally maintained substitution from levels to universes.
  @return A canonical universe: each level in the universe is canonical w.r.t. the given model. *)
val normalize : t -> Level.t -> Universe.t option

val normalize_subst : t -> t

exception InconsistentEquality
exception OccurCheck
exception NotCanonical

(** [set idx u model] substitutes universe [u] for all occurrences of [idx] in model, resulting
in a set of constraints that no longer mentions [idx]. This is a stronger than [enforce_eq idx u],
as the [idx] universe is dropped from the constraints altogether. Returns a list of universes
that are also made equal by the new constraint and are also substituted by [u] in the resulting graph.
  @raise InconsistentEquality if setting [l = u] results in an unsatisfiable constraint
  @raise OccurCheck if the universe contains the level, up to equivalence in the graph
  @raise NotCanonical if the given level to set is not canonical *)
val set : Level.t -> Universe.t -> t -> t * level_equivalences

type extended_constraint_type =
  | ULe | ULt | UEq

type explanation = Universe.t * (extended_constraint_type * Universe.t) list

val get_explanation : UnivConstraint.t -> t -> explanation
(** Assuming that the corresponding call to [enforce_*] returned [None], this
    will give a trace for the failure. *)

type 'a constraint_fold = UnivConstraint.t -> 'a -> 'a

(** [constraints_of graph ?only_local fold acc = (levels, acc', equivs)]

  Computes the constraints modeled by the graph.
  If [only_local] is [true] (default is [false]), [levels] is the set of universes that were declared locally
  (since the last and only possible [set_local] call on the graph).
  The [Le] constraints are passed to a folding function starting with [acc] whose result is returned as [acc'].
  Finally [equivs] contains a level substitution corresponding to [Eq] constraints. *)
val constraints_of : t -> ?only_local:bool -> 'a constraint_fold -> 'a ->
  Level.Set.t * 'a * (locality * Universe.t) Level.Map.t

val constraints_for : kept:Level.Set.t -> t -> 'a constraint_fold -> 'a -> 'a

val remove : Level.Set.t -> t -> t
(** [remove l m] Remove the [l] nodes and constraints mentionning [l] from [m] *)

val domain : t -> Level.Set.t
(** Return the set of registered universe variables *)

val variables : local:bool -> with_subst:bool -> t -> Level.Set.t
(** Computes the set of registered variables, optionally restricted to local ones, and
  optionally including the substituted variables. *)

val subst : local:bool -> t -> (locality * Universe.t) Level.Map.t
(** Substitution from (local) levels to universes.
   N.B.: slighty expensive to compute, better use [normalize] below. *)

val switch_locality : Level.t -> t -> t

val is_local : Level.t -> t -> bool

(* val choose : (Level.t -> bool) -> t -> Level.t -> Level.t option *)

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
| Alias of Universe.t
| Node of (int * Universe.t) list (** Nodes [(k_i, u_i); ...] s.t. u + k_i <= u_i *)

type repr = node Level.Map.t

(** Get a representation of the model, optionally selecting only local universes and constraints. *)
val repr : local:bool -> t -> repr

(* Print the model. Optionally print only the local universes and constraints. *)
val pr_model : ?local:bool -> t -> Pp.t

val valuation : t -> int Level.Map.t
