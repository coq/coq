(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Stateid
open Vernacexpr

val string_of_vernac_classification : vernac_classification -> string

(** What does a vernacular do *)
val classify_vernac : vernac_expr -> vernac_classification

(** Install an additional vernacular classifier (that has precedence over
    all classifiers already installed) *)
val declare_vernac_classifier :
  string -> (vernac_expr -> vernac_classification) -> unit
