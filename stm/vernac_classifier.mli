(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Vernacexpr

val string_of_vernac_classification : vernac_classification -> string

(** What does a vernacular do *)
val classify_vernac : vernac_control -> vernac_classification

(** Standard constant classifiers *)
val classify_as_query : vernac_classification
val classify_as_sideeff : vernac_classification
val classify_as_proofstep : vernac_classification

val stm_allow_nested_proofs_option_name : string list
