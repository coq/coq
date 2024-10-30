(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

Require Import PreOmega ZMicromega RingMicromega VarMap DeclConstant.
Require Import BinNums.
Require Stdlib.micromega.Tauto.
Declare ML Module "rocq-runtime.plugins.micromega_core".
Declare ML Module "rocq-runtime.plugins.micromega".

Ltac zchecker :=
  let __wit := fresh "__wit" in
  let __varmap := fresh "__varmap" in
  let __ff := fresh "__ff" in
  intros __wit __varmap __ff ;
  exact (ZTautoChecker_sound __ff __wit
                                (@eq_refl bool true <: @eq bool (ZTautoChecker __ff __wit) true)
                                (@find Z Z0 __varmap)).

Ltac lia := Zify.zify; xlia zchecker.

Ltac nia := Zify.zify; xnia zchecker.
