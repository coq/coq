(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Glob_term

(** Equalities *)

val cases_pattern_eq : cases_pattern -> cases_pattern -> bool

val glob_constr_eq : glob_constr -> glob_constr -> bool

(** Operations on [glob_constr] *)

val cases_pattern_loc : cases_pattern -> Loc.t

val cases_predicate_names : tomatch_tuples -> Name.t list

(** Apply one argument to a glob_constr *)
val mkGApp : Loc.t -> glob_constr -> glob_constr -> glob_constr

val map_glob_constr :
  (glob_constr -> glob_constr) -> glob_constr -> glob_constr

(** Ensure traversal from left to right *)
val map_glob_constr_left_to_right :
  (glob_constr -> glob_constr) -> glob_constr -> glob_constr

val fold_glob_constr : ('a -> glob_constr -> 'a) -> 'a -> glob_constr -> 'a
val iter_glob_constr : (glob_constr -> unit) -> glob_constr -> unit
val occur_glob_constr : Id.t -> glob_constr -> bool
val free_glob_vars : glob_constr -> Id.t list
val loc_of_glob_constr : glob_constr -> Loc.t

(** [map_pattern_binders f m c] applies [f] to all the binding names
    in a pattern-matching expression ({!Glob_term.GCases}) represented
    here by its relevant components [m] and [c]. It is used to
    interpret Ltac-bound names both in pretyping and printing of
    terms. *)
val map_pattern_binders : (name -> name) ->
  tomatch_tuples -> cases_clauses -> (tomatch_tuples*cases_clauses)

(** [map_pattern f m c] applies [f] to the return predicate and the
    right-hand side of a pattern-matching expression
    ({!Glob_term.GCases}) represented here by its relevant components
    [m] and [c]. *)
val map_pattern : (glob_constr -> glob_constr) ->
  tomatch_tuples -> cases_clauses -> (tomatch_tuples*cases_clauses)

(** Conversion from glob_constr to cases pattern, if possible

    Take the current alias as parameter,
    @raise Not_found if translation is impossible *)
val cases_pattern_of_glob_constr : Name.t -> glob_constr -> cases_pattern

val glob_constr_of_closed_cases_pattern : cases_pattern -> Name.t * glob_constr
