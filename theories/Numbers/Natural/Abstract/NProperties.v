(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export NAxioms.
Require Import NMaxMin NParity NPow NSqrt NDiv.

(** This functor summarizes all known facts about N. *)

Module Type NProp (N:NAxiomsSig) :=
 NMaxMinProp N <+ NParityProp N <+ NPowProp N <+ NSqrtProp N <+ NDivProp N.
