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

(** * String notation *)

val vernac_string_notation : locality_flag ->
                             qualid ->
                             qualid -> qualid ->
                             Number.number_string_via option ->
                             Notation_term.scope_name -> unit
