(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Notation_term
open Glob_term

(** Utilities about [notation_constr] *)

(** Translate a [glob_constr] into a notation given the list of variables
    bound by the notation; also interpret recursive patterns           *)

val notation_constr_of_glob_constr : notation_interp_env ->
  glob_constr -> notation_constr

(** Name of the special identifier used to encode recursive notations  *)
val ldots_var : Id.t

(** Equality of [glob_constr] (warning: only partially implemented) *)
(** FIXME: nothing to do here *)
val eq_glob_constr : glob_constr -> glob_constr -> bool

(** Re-interpret a notation as a [glob_constr], taking care of binders     *)

val glob_constr_of_notation_constr_with_binders : Loc.t ->
  ('a -> Name.t -> 'a * Name.t) ->
  ('a -> notation_constr -> glob_constr) ->
  'a -> notation_constr -> glob_constr

val glob_constr_of_notation_constr : Loc.t -> notation_constr -> glob_constr

(** [match_notation_constr] matches a [glob_constr] against a notation
    interpretation; raise [No_match] if the matching fails   *)

exception No_match

val match_notation_constr : bool -> glob_constr -> interpretation ->
      (glob_constr * subscopes) list * (glob_constr list * subscopes) list *
      (glob_decl list * subscopes) list

val match_notation_constr_cases_pattern :
  cases_pattern -> interpretation ->
  ((cases_pattern * subscopes) list * (cases_pattern list * subscopes) list) *
    (int * cases_pattern list)

val match_notation_constr_ind_pattern :
  inductive -> cases_pattern  list -> interpretation ->
  ((cases_pattern * subscopes) list * (cases_pattern list * subscopes) list) *
    (int * cases_pattern list)

(** Substitution of kernel names in interpretation data                *)

val subst_interpretation :
  Mod_subst.substitution -> interpretation -> interpretation

val add_patterns_for_params : inductive -> cases_pattern list -> cases_pattern list
