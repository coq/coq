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

type t

val empty : t

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

val enforce_eq : Universe.t -> Universe.t -> t -> t option
val enforce_leq : Universe.t -> Universe.t -> t -> t option
val enforce_lt : Universe.t -> Universe.t -> t -> t option
val enforce_constraint : univ_constraint -> t -> t option

exception InconsistentEquality

(** [set idx u model] substitutes universe [u] for all occurrences of [idx] in model, resulting
in a set of constraints that no longer mentions [idx]. This is a stronger than [enforce_eq idx u],
as the [idx] universe is dropped from the constraints altogether.
  @raise InconsistentEquality if setting [l = u] results in an unsatisfiable constraint *)
val set : Level.t -> Universe.t -> t -> t

type extended_constraint_type =
  | ULe | ULt | UEq

type explanation = Universe.t * (extended_constraint_type * Universe.t) list

val get_explanation : univ_constraint -> t -> explanation
(** Assuming that the corresponding call to [enforce_*] returned [None], this
    will give a trace for the failure. *)

type 'a constraint_fold = univ_constraint -> 'a -> 'a

val constraints_of : t -> 'a constraint_fold -> 'a -> 'a * LevelExpr.Set.t list

val constraints_for : kept:Level.Set.t -> t -> 'a constraint_fold -> 'a -> 'a

val domain : t -> Level.Set.t

val choose : (Level.t -> bool) -> t -> Level.t -> Level.t option

(* val minimize : t -> Level.t -> t * (Level.t * int) list *)

(** {5 High-level representation} *)

type node =
| Alias of LevelExpr.t
| Node of (int * Universe.t) list (** Nodes [(k_i, u_i); ...] s.t. u + k_i <= u_i *)

type repr = node Level.Map.t

val repr : t -> repr

(* New functions *)
val pr_model : t -> Pp.t

val valuation : t -> int Level.Map.t
