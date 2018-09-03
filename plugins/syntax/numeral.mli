(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Libnames
open Constrexpr
open Vernacexpr

(** * Numeral notation *)

type numnot_option =
  | Nop
  | Warning of raw_natural_number
  | Abstract of raw_natural_number

val vernac_numeral_notation : locality_flag -> qualid -> qualid -> qualid -> Notation_term.scope_name -> numnot_option -> unit
