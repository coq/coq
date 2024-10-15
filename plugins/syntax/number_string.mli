(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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


type number_string_via = qualid * (bool * qualid * qualid) list

(** * Number notation *)

type number_option =
  | After of numnot_option
  | Via of number_string_via

val vernac_number_notation : locality_flag ->
                             qualid ->
                             qualid -> qualid ->
                             number_option list ->
                             Notation_term.scope_name -> unit

(** * String notation *)

val vernac_string_notation : locality_flag ->
                             qualid ->
                             qualid -> qualid ->
                             number_string_via option ->
                             Notation_term.scope_name -> unit
