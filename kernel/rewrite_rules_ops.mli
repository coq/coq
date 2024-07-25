(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations

type pattern_translation_error =
  | UnknownEvar
  | UnknownQVar of Sorts.QVar.t
  | UnknownLevel of Univ.Level.t
  | DuplicatePatVar of Evar.t * Names.Id.t * int * int
  | DuplicateQVar of Sorts.QVar.t * int * int
  | DuplicateUVar of Univ.Level.t * int * int
  | NoHeadSymbol

exception PatternTranslationError of pattern_translation_error

val translate_rewrite_rule : Environ.env -> rewrite_rule -> Names.Constant.t * machine_rewrite_rule

val head_symbol : pattern -> Names.Constant.t
