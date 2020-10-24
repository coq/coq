(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Notation_term
open Glob_term

(** {5 Utilities about [notation_constr]} *)

val eq_notation_constr : Id.t list * Id.t list -> notation_constr -> notation_constr -> bool

val strictly_finer_notation_constr : Id.t list * Id.t list -> notation_constr -> notation_constr -> bool
(** Tell if [t1] is a strict refinement of [t2]
    (this is a partial order and returning [false] does not mean that
    [t2] is finer than [t1]) *)

(** Substitution of kernel names in interpretation data                *)

val subst_interpretation :
  Mod_subst.substitution -> interpretation -> interpretation

(** Name of the special identifier used to encode recursive notations  *)

val ldots_var : Id.t

(** {5 Translation back and forth between [glob_constr] and [notation_constr]} *)

(** Translate a [glob_constr] into a notation given the list of variables
    bound by the notation; also interpret recursive patterns           *)

val notation_constr_of_glob_constr : notation_interp_env ->
  glob_constr -> notation_constr * reversibility_status

(** Re-interpret a notation as a [glob_constr], taking care of binders *)

type 'a binder_status_fun = {
  no : 'a -> 'a;
  restart_prod : 'a -> 'a;
  restart_lambda : 'a -> 'a;
  switch_prod : 'a -> 'a;
  switch_lambda : 'a -> 'a;
  slide : 'a -> 'a;
}

val apply_cases_pattern : ?loc:Loc.t ->
  (Id.t list * cases_pattern_disjunction) * Id.t -> glob_constr -> glob_constr

val glob_constr_of_notation_constr_with_binders : ?loc:Loc.t ->
  ('a -> Name.t -> glob_constr option -> 'a * ((Id.t list * cases_pattern_disjunction) * Id.t) option * Name.t * Glob_term.binding_kind * glob_constr option) ->
  ('a -> notation_constr -> glob_constr) -> ?h:'a binder_status_fun ->
  'a -> notation_constr -> glob_constr

val glob_constr_of_notation_constr : ?loc:Loc.t -> notation_constr -> glob_constr

(** {5 Matching a notation pattern against a [glob_constr]} *)

(** [match_notation_constr] matches a [glob_constr] against a notation
    interpretation; raise [No_match] if the matching fails   *)

exception No_match

val print_parentheses : bool ref

val match_notation_constr : print_univ:bool -> 'a glob_constr_g -> vars:Id.Set.t -> interpretation ->
      ((Id.Set.t * 'a glob_constr_g) * extended_subscopes) list *
      ((Id.Set.t * 'a glob_constr_g list) * extended_subscopes) list *
      ((Id.Set.t * 'a cases_pattern_disjunction_g) * extended_subscopes) list *
      ((Id.Set.t * 'a extended_glob_local_binder_g list) * extended_subscopes) list

val match_notation_constr_cases_pattern :
  'a cases_pattern_g -> interpretation ->
  (('a cases_pattern_g * extended_subscopes) list * ('a cases_pattern_g list * extended_subscopes) list) *
    (bool * int * 'a cases_pattern_g list)

val match_notation_constr_ind_pattern :
  inductive -> 'a cases_pattern_g list -> interpretation ->
  (('a cases_pattern_g * extended_subscopes) list * ('a cases_pattern_g list * extended_subscopes) list) *
    (bool * int * 'a cases_pattern_g list)

(** {5 Matching a notation pattern against a [glob_constr]} *)

