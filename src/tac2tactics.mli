(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Misctypes
open Tactypes
open Proofview

(** Local reimplementations of tactics variants from Coq *)

val apply : advanced_flag -> evars_flag ->
  EConstr.constr with_bindings tactic list ->
  (Id.t * intro_pattern option) option -> unit tactic
