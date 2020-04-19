(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Typeclasses

type hint_info_expr = Constrexpr.constr_pattern_expr hint_info_gen

type reference_or_constr =
  | HintsReference of Libnames.qualid
  | HintsConstr of Constrexpr.constr_expr

type hints_expr =
  | HintsResolve of (hint_info_expr * bool * reference_or_constr) list
  | HintsResolveIFF of bool * Libnames.qualid list * int option
  | HintsImmediate of reference_or_constr list
  | HintsUnfold of Libnames.qualid list
  | HintsTransparency of Libnames.qualid Hints.hints_transparency_target * bool
  | HintsMode of Libnames.qualid * Hints.hint_mode list
  | HintsConstructors of Libnames.qualid list
  | HintsExtern of int * Constrexpr.constr_expr option * Genarg.raw_generic_argument

val interp_hints : poly:bool -> hints_expr -> Hints.hints_entry
