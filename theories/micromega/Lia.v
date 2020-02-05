(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
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
Require Import ZArith_base.
Require Import RingMicromega.
Require Import VarMap.
Require Import DeclConstant.
Require Coq.micromega.Tauto.
Declare ML Module "micromega_plugin".


Ltac zchecker :=
  intros __wit __varmap __ff ;
  exact (ZTautoChecker_sound __ff __wit
                                (@eq_refl bool true <: @eq bool (ZTautoChecker __ff __wit) true)
                                (@find Z Z0 __varmap)).

Ltac lia := PreOmega.zify; xlia zchecker.
               
Ltac nia := PreOmega.zify; xnlia zchecker.


(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
