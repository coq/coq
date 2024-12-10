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
(*  Frédéric Besson (Irisa/Inria)      2016                             *)
(*                                                                      *)
(************************************************************************)

Require Import RMicromega.
Require Import QMicromega.
Require Import Rdefinitions.
Require Import RingMicromega.
Require Import VarMap.
Require Stdlib.micromega.Tauto.
Require Import Rregisternames.

Declare ML Module "rocq-runtime.plugins.micromega".

Ltac rchange :=
  let __wit := fresh "__wit" in
  let __varmap := fresh "__varmap" in
  let __ff := fresh "__ff" in
  intros __wit __varmap __ff ;
  change (Tauto.eval_bf (Reval_formula (@find R 0%R __varmap)) __ff) ;
  apply (RTautoChecker_sound __ff __wit).

Ltac rchecker_no_abstract := rchange ; vm_compute ; reflexivity.
Ltac rchecker_abstract := rchange ; vm_cast_no_check (eq_refl true).

Ltac rchecker := rchecker_no_abstract.

(** Here, lra stands for linear real arithmetic *)
Ltac lra := unfold Rdiv in * ; xlra_R rchecker.

(** Here, nra stands for non-linear real arithmetic *)
Ltac nra := unfold Rdiv in * ; xnra_R rchecker.

Ltac xpsatz dom d :=
  let tac := lazymatch dom with
  | R =>
    (xsos_R rchecker) || (xpsatz_R d rchecker)
  | _ => fail "Unsupported domain"
 end in tac.

Tactic Notation "psatz" constr(dom) int_or_var(n) := xpsatz dom n.
Tactic Notation "psatz" constr(dom) := xpsatz dom ltac:(-1).

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
