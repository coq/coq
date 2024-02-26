(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val wit_fun_ind_using :
  (Constrexpr.constr_expr Tactypes.with_bindings option,
   Genintern.glob_constr_and_expr Tactypes.with_bindings option,
   EConstr.constr Tactypes.with_bindings Tactypes.delayed_open option)
  Genarg.genarg_type

val fun_ind_using :
  Constrexpr.constr_expr Tactypes.with_bindings option Pcoq.Entry.t

val wit_with_names :
  (Constrexpr.constr_expr Tactypes.intro_pattern_expr CAst.t option,
   Genintern.glob_constr_and_expr Tactypes.intro_pattern_expr CAst.t option,
   Tactypes.intro_pattern option)
  Genarg.genarg_type

val with_names :
  Constrexpr.constr_expr Tactypes.intro_pattern_expr CAst.t option
  Pcoq.Entry.t

val wit_constr_comma_sequence' :
  (Constrexpr.constr_expr list, Genintern.glob_constr_and_expr list,
   EConstr.constr list)
  Genarg.genarg_type

val constr_comma_sequence' : Constrexpr.constr_expr list Pcoq.Entry.t

val wit_auto_using' :
  (Constrexpr.constr_expr list, Genintern.glob_constr_and_expr list,
   EConstr.constr list)
  Genarg.genarg_type

val auto_using' : Constrexpr.constr_expr list Pcoq.Entry.t

val wit_function_fix_definition :
  Vernacexpr.fixpoint_expr Loc.located Genarg.uniform_genarg_type

val function_fix_definition :
  Vernacexpr.fixpoint_expr Loc.located Pcoq.Entry.t

val wit_fun_scheme_arg :
  (Names.Id.t * Libnames.qualid * Sorts.family) Genarg.vernac_genarg_type

val fun_scheme_arg :
  (Names.Id.t * Libnames.qualid * Sorts.family) Pcoq.Entry.t
