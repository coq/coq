(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Genarg
open Ltac2_plugin.Tac2expr

val wit_ltac2in1 : (Id.t CAst.t list * raw_tacexpr, Id.t list * glb_tacexpr, Util.Empty.t) genarg_type
(** Ltac2 quotations in Ltac1 code *)

val wit_ltac2in1_val : (Id.t CAst.t list * raw_tacexpr, glb_tacexpr, Util.Empty.t) genarg_type
(** Ltac2 quotations in Ltac1 returning Ltac1 values.
    When ids are bound interning turns them into Ltac1.lambda. *)

val wit_ltac2_val : (Util.Empty.t, unit, Util.Empty.t) genarg_type
(** Embedding Ltac2 closures of type [Ltac1.t -> Ltac1.t] inside Ltac1. There is
    no relevant data because arguments are passed by conventional names. *)
