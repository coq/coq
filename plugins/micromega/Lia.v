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
Require Import ZArith_base.
Require Import RingMicromega.
Require Import VarMap.
Require Import Zify.
Require Coq.micromega.Tauto.
Declare ML Module "micromega_plugin".

Hint Resolve Z.le_refl Z.add_comm Z.add_assoc Z.mul_comm Z.mul_assoc Z.add_0_l
  Z.add_0_r Z.mul_1_l Z.add_opp_diag_l Z.add_opp_diag_r Z.mul_add_distr_r
  Z.mul_add_distr_l: zarith.

Require Export Zhints.

Ltac preprocess :=
  intros;
  let T := match goal with |- ?P => P end in let s := type of T in
  match s with
  | Prop => zify ; unfold Z.succ in * ; unfold Z.pred in *
  | _ => exfalso; zify ; unfold Z.succ in * ; unfold Z.pred in *
  end.

Ltac zchange := 
  intros __wit __varmap __ff ;
  change (Tauto.eval_f (Zeval_formula (@find Z Z0 __varmap)) __ff) ;
  apply (ZTautoChecker_sound __ff __wit).

Ltac zchecker_no_abstract := zchange ; vm_compute ; reflexivity.

Ltac zchecker_abstract := zchange ; vm_cast_no_check (eq_refl true).

Ltac zchecker := zchecker_no_abstract.

Ltac lia := preprocess; xlia zchecker.
               
Ltac nia := preprocess; xnlia zchecker.

Hint Extern 10 (_ = _ :>nat) => abstract lia: zarith.
Hint Extern 10 (_ <= _) => abstract lia: zarith.
Hint Extern 10 (_ < _) => abstract lia: zarith.
Hint Extern 10 (_ >= _) => abstract lia: zarith.
Hint Extern 10 (_ > _) => abstract lia: zarith.

Hint Extern 10 (_ <> _ :>nat) => abstract lia: zarith.
Hint Extern 10 (~ _ <= _) => abstract lia: zarith.
Hint Extern 10 (~ _ < _) => abstract lia: zarith.
Hint Extern 10 (~ _ >= _) => abstract lia: zarith.
Hint Extern 10 (~ _ > _) => abstract lia: zarith.

Hint Extern 10 (_ = _ :>Z) => abstract lia: zarith.
Hint Extern 10 (_ <= _)%Z => abstract lia: zarith.
Hint Extern 10 (_ < _)%Z => abstract lia: zarith.
Hint Extern 10 (_ >= _)%Z => abstract lia: zarith.
Hint Extern 10 (_ > _)%Z => abstract lia: zarith.

Hint Extern 10 (_ <> _ :>Z) => abstract lia: zarith.
Hint Extern 10 (~ (_ <= _)%Z) => abstract lia: zarith.
Hint Extern 10 (~ (_ < _)%Z) => abstract lia: zarith.
Hint Extern 10 (~ (_ >= _)%Z) => abstract lia: zarith.
Hint Extern 10 (~ (_ > _)%Z) => abstract lia: zarith.

Hint Extern 10 False => abstract lia: zarith.

Ltac omega := lia.


(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
