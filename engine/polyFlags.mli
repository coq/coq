(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t
(** Set of flags for universe polymorphism, implicit sort polymorphism and cumulativity.
    Note that implicit sort polymorphism (not collapsing sort variables to Type) and
    cumulativity only make sense for constructions that are already polymorphic.
    This invariant is ensured by the smart constructor below.
 *)

(** Raises a user error if [univ_poly = false] and either [collapse_sort_variables = false] or [cumulative = true]. *)
val make : univ_poly:bool -> collapse_sort_variables:bool -> cumulative:bool -> t

(** The [default] is monomorphic:
    [univ_poly] and [cumulative] are [false], [collapse_sort_variables] is [true] *)
val default : t

(** Only sets the universe [univ_poly] flag.
    Use with care, this probably indicates that the code does not handle
    [cumulative] constructions when it should. Code relying on elaboration should
    also support the [collapse_sort_variables] flag. *)
val of_univ_poly : bool -> t

(** Accessors *)
val univ_poly : t -> bool
val collapse_sort_variables : t -> bool
val cumulative : t -> bool

val set_solve_term_variables : t -> t
val solve_term_variables : t -> bool

(** Pretty print *)
val pr : t -> Pp.t

(** Used to have distinguished default behaviors when treating assumptions/axioms,
    definitions or inductives *)
type construction_kind =
  Assumption | Definition | Inductive
