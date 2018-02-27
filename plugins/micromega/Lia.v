(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

Require Import ZMicromega.
Require Import ZArith.
Require Import RingMicromega.
Require Import VarMap.
Require Coq.micromega.Tauto.
Declare ML Module "micromega_plugin".


Ltac preprocess :=
  zify ; unfold Z.succ in * ; unfold Z.pred in *.

Ltac zchange := 
  intros __wit __varmap __ff ;
  change (Tauto.eval_f (Zeval_formula (@find Z Z0 __varmap)) __ff) ;
  apply (ZTautoChecker_sound __ff __wit).

Ltac zchecker_no_abstract := zchange ; vm_compute ; reflexivity.

Ltac zchecker_abstract := zchange ; vm_cast_no_check (eq_refl true).

Ltac zchecker := zchecker_no_abstract.

Ltac lia := preprocess; xlia zchecker.
               
Ltac nia := preprocess; xnlia zchecker.


(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
