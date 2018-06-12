(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Basic generic arguments. *)

open Loc
open Names
open EConstr
open Libnames
open Genredexpr
open Pattern
open Constrexpr
open Genarg
open Genintern
open Locus

type 'a and_short_name = 'a * lident option

val wit_unit : unit uniform_genarg_type

val wit_bool : bool uniform_genarg_type

val wit_int : int uniform_genarg_type

val wit_string : string uniform_genarg_type

val wit_pre_ident : string uniform_genarg_type

(** {5 Additional generic arguments} *)

val wit_int_or_var : (int or_var, int or_var, int) genarg_type

val wit_ident : Id.t uniform_genarg_type

val wit_var : (lident, lident, Id.t) genarg_type

val wit_ref : (qualid, GlobRef.t located or_var, GlobRef.t) genarg_type

val wit_sort_family : (Sorts.family, unit, unit) genarg_type

val wit_constr : (constr_expr, glob_constr_and_expr, constr) genarg_type

val wit_uconstr : (constr_expr , glob_constr_and_expr, Ltac_pretype.closed_glob_constr) genarg_type

val wit_open_constr :
  (constr_expr, glob_constr_and_expr, constr) genarg_type

val wit_red_expr :
  ((constr_expr,qualid or_by_notation,constr_expr) red_expr_gen,
  (glob_constr_and_expr,evaluable_global_reference and_short_name or_var,glob_constr_pattern_and_expr) red_expr_gen,
  (constr,evaluable_global_reference,constr_pattern) red_expr_gen) genarg_type

val wit_clause_dft_concl :  (lident Locus.clause_expr, lident Locus.clause_expr, Names.Id.t Locus.clause_expr) genarg_type

(** Aliases for compatibility *)

val wit_integer : int uniform_genarg_type
val wit_preident : string uniform_genarg_type
val wit_reference : (qualid, GlobRef.t located or_var, GlobRef.t) genarg_type
val wit_global : (qualid, GlobRef.t located or_var, GlobRef.t) genarg_type
val wit_clause :  (lident Locus.clause_expr, lident Locus.clause_expr, Names.Id.t Locus.clause_expr) genarg_type
val wit_redexpr :
  ((constr_expr,qualid or_by_notation,constr_expr) red_expr_gen,
  (glob_constr_and_expr,evaluable_global_reference and_short_name or_var,glob_constr_pattern_and_expr) red_expr_gen,
  (constr,evaluable_global_reference,constr_pattern) red_expr_gen) genarg_type
