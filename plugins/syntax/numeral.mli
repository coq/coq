(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Libnames
open Vernacexpr
open Notation

(** * Numeral notation *)

val vernac_numeral_notation : locality_flag ->
                              qualid -> qualid -> qualid ->
                              Notation_term.scope_name -> numnot_option -> unit
