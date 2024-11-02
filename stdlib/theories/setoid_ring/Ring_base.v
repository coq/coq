(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This module gathers the necessary base to build an instance of the
   ring tactic. Abstract rings need more theory, depending on
   BinInt. *)

Declare ML Module "rocq-runtime.plugins.ring".
Require Export Ring_theory.
Require Export Ring_tac.
Require Import InitialRing.
