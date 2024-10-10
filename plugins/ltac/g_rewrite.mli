(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type constr_expr_with_bindings =
    Constrexpr.constr_expr Tactypes.with_bindings

type glob_constr_with_bindings =
    Genintern.glob_constr_and_expr Tactypes.with_bindings

type glob_constr_with_bindings_sign =
    Geninterp.interp_sign *
    Genintern.glob_constr_and_expr Tactypes.with_bindings

val wit_glob_constr_with_bindings :
  (constr_expr_with_bindings,
   glob_constr_with_bindings,
   glob_constr_with_bindings_sign)
  Genarg.genarg_type

val glob_constr_with_bindings :
  constr_expr_with_bindings Pcoq.Entry.t

val wit_rewstrategy :
  (Tacexpr.raw_strategy, Tacexpr.glob_strategy, Rewrite.strategy) Genarg.genarg_type

val rewstrategy : Tacexpr.raw_strategy Pcoq.Entry.t

type binders_argtype = Constrexpr.local_binder_expr list

val wit_binders : binders_argtype Genarg.vernac_genarg_type

val binders : binders_argtype Pcoq.Entry.t
