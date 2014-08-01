(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria)      2013                             *)
(*                                                                      *)
(************************************************************************)

Require Import ZMicromega.
Require Import ZArith.
Require Import RingMicromega.
Require Import VarMap.
Require Tauto.
Declare ML Module "micromega_plugin".

Ltac preprocess :=
  zify ; unfold Z.succ in * ; unfold Z.pred in *.

Ltac lia :=
  preprocess;
  (*cbv delta - [Z.add Z.sub Z.opp Z.mul Z.pow Z.gt Z.ge Z.le Z.lt iff not] ;*) xlia ;
  abstract (
      intros __wit __varmap __ff ;
      change (Tauto.eval_f (Zeval_formula (@find Z Z0 __varmap)) __ff) ;
      apply (ZTautoChecker_sound __ff __wit); vm_compute ; reflexivity).

Ltac nia :=
  preprocess;
  xnlia ;
  abstract (
  intros __wit __varmap __ff ;
    change (Tauto.eval_f (Zeval_formula (@find Z Z0 __varmap)) __ff) ;
      apply (ZTautoChecker_sound __ff __wit); vm_compute ; reflexivity).


(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
