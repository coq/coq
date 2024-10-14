(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Tacexpr
open Mod_subst
open Genarg
open Genintern
open Tactypes

(** Substitution of tactics at module closing time *)

val subst_tactic : substitution -> glob_tactic_expr -> glob_tactic_expr

(** For generic arguments, we declare and store substitutions
    in a table *)

val subst_genarg : substitution -> glob_generic_argument -> glob_generic_argument

(** Misc *)

val subst_glob_constr_and_expr :
  substitution -> glob_constr_and_expr -> glob_constr_and_expr

val subst_glob_with_bindings : substitution ->
  glob_constr_and_expr with_bindings ->
  glob_constr_and_expr with_bindings

val subst_glob_red_expr : substitution -> Genredexpr.glob_red_expr -> Genredexpr.glob_red_expr
