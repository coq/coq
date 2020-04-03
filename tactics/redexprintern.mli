(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val intern_constr_with_occurrences :
  Genintern.glob_sign ->
  'a * Constrexpr.constr_expr ->
  'a * (Glob_term.glob_constr * Constrexpr.constr_expr option)
val intern_red_expr :
  Genintern.glob_sign ->
  (Constrexpr.constr_expr, Libnames.qualid Constrexpr.or_by_notation,
   Constrexpr.constr_pattern_expr)
  Genredexpr.red_expr_gen ->
  (Glob_term.glob_constr * Constrexpr.constr_expr option,
   (Names.evaluable_global_reference * Names.Id.t CAst.t option) Locus.or_var,
   Names.Id.Set.t * (Glob_term.glob_constr * Constrexpr.constr_expr option) *
   Pattern.constr_pattern)
  Genredexpr.red_expr_gen
