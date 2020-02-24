(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val intern_constr_gen :
  bool ->
  bool ->
  Genintern.glob_sign ->
  Constrexpr.constr_expr ->
  Glob_term.glob_constr * Constrexpr.constr_expr option
val intern_constr :
  Genintern.glob_sign ->
  Constrexpr.constr_expr ->
  Glob_term.glob_constr * Constrexpr.constr_expr option
val intern_type :
  Genintern.glob_sign ->
  Constrexpr.constr_expr ->
  Glob_term.glob_constr * Constrexpr.constr_expr option
val intern_typed_pattern :
  Genintern.glob_sign ->
  as_type:bool ->
  ltacvars:Names.Id.Set.t ->
  Constrexpr.constr_pattern_expr ->
  Pattern.patvar list *
  (Names.Id.Set.t * (Glob_term.glob_constr * Constrexpr.constr_expr option) *
   Pattern.constr_pattern)
