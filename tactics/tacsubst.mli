(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Tacexpr
open Mod_subst
open Genarg
open Misctypes

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
