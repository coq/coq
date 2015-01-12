(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This module gathers the necessary base to build an instance of the
   ring tactic. Abstract rings need more theory, depending on
   ZArith_base. *)

Require Import Quote.
Declare ML Module "newring_plugin".
Require Export Ring_theory.
Require Export Ring_tac.
Require Import InitialRing.
