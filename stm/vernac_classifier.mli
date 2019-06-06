(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Vernacextend

val string_of_vernac_classification : vernac_classification -> string

(** What does a vernacular do *)
val classify_vernac : Vernacexpr.vernac_control -> vernac_classification

(**  *)
val stm_allow_nested_proofs_option_name : string list
