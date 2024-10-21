(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ltac2_plugin
open Tac2expr

type notation_interpretation_data

val register_ltac1_notation : Attributes.vernac_flags -> sexpr list ->
  int option -> raw_tacexpr -> notation_interpretation_data

val register_ltac1_notation_interpretation : notation_interpretation_data -> unit
