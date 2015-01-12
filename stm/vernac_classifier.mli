(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Vernacexpr
open Genarg

val string_of_vernac_classification : vernac_classification -> string

(** What does a vernacular do *)
val classify_vernac : vernac_expr -> vernac_classification

(** Install a vernacular classifier for VernacExtend *)
val declare_vernac_classifier :
  Vernacexpr.extend_name -> (raw_generic_argument list -> unit -> vernac_classification) -> unit

(** Set by Stm *)
val set_undo_classifier : (vernac_expr -> vernac_classification) -> unit

(** Standard constant classifiers *)
val classify_as_query : vernac_classification
val classify_as_sideeff : vernac_classification
val classify_as_proofstep : vernac_classification

