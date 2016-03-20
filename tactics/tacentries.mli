(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Vernacexpr
open Tacexpr

(** Adding a tactic notation in the environment *)

val add_tactic_notation :
  locality_flag * int * grammar_tactic_prod_item_expr list * raw_tactic_expr ->
    unit

val add_ml_tactic_notation : ml_tactic_name ->
  Tacexpr.raw_tactic_expr Egramml.grammar_prod_item list list -> unit
