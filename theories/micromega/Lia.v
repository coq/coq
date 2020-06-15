(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria)      2013-2016                        *)
(*                                                                      *)
(************************************************************************)

Require Import ZMicromega RingMicromega VarMap DeclConstant.
Require Import BinNums.
Require Coq.micromega.Tauto.
Declare ML Module "micromega_plugin".

Ltac zchecker :=
  intros ?__wit ?__varmap ?__ff ;
  exact (ZTautoChecker_sound __ff __wit
                                (@eq_refl bool true <: @eq bool (ZTautoChecker __ff __wit) true)
                                (@find Z Z0 __varmap)).

Ltac lia := Zify.zify; xlia zchecker.
               
Ltac nia := Zify.zify; xnlia zchecker.

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
