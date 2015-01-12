(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

Require Import ZMicromega.
Require Import QMicromega.
Require Import RMicromega.
Require Import QArith.
Require Import ZArith.
Require Import Rdefinitions.
Require Import RingMicromega.
Require Import VarMap.
Require Tauto.
Declare ML Module "micromega_plugin".

Ltac preprocess := 
    zify ; unfold Z.succ in * ; unfold Z.pred in *.

Ltac lia :=
  preprocess;
  xlia ;
  abstract (
  intros __wit __varmap __ff ;
    change (Tauto.eval_f (Zeval_formula (@find Z Z0 __varmap)) __ff) ;
      apply (ZTautoChecker_sound __ff __wit); vm_cast_no_check (eq_refl true)).

Ltac nia :=
  preprocess;
  xnlia ;
  abstract (
  intros __wit __varmap __ff ;
    change (Tauto.eval_f (Zeval_formula (@find Z Z0 __varmap)) __ff) ;
      apply (ZTautoChecker_sound __ff __wit); vm_cast_no_check (eq_refl true)).


Ltac xpsatz dom d :=
  let tac := lazymatch dom with
  | Z =>
    (sos_Z || psatz_Z d) ;
      abstract(
    intros __wit __varmap __ff ;
    change (Tauto.eval_f (Zeval_formula (@find Z Z0 __varmap)) __ff) ;
    apply (ZTautoChecker_sound __ff __wit); vm_cast_no_check (eq_refl true))
  | R =>
    (sos_R || psatz_R d) ;
    (* If csdp is not installed, the previous step might not produce any
    progress: the rest of the tactical will then fail. Hence the 'try'. *)
    try (abstract(intros __wit __varmap __ff ;
        change (Tauto.eval_f (Reval_formula (@find R 0%R __varmap)) __ff) ;
        apply (RTautoChecker_sound __ff __wit); vm_cast_no_check (eq_refl true)))
  | Q =>
    (sos_Q || psatz_Q d) ;
    (* If csdp is not installed, the previous step might not produce any
    progress: the rest of the tactical will then fail. Hence the 'try'. *)
    try  (abstract(intros __wit __varmap __ff ;
        change (Tauto.eval_f (Qeval_formula (@find Q 0%Q __varmap)) __ff) ;
        apply (QTautoChecker_sound __ff __wit); vm_cast_no_check (eq_refl true)))
  | _ => fail "Unsupported domain"
  end in tac.

Tactic Notation "psatz" constr(dom) int_or_var(n) := xpsatz dom n.
Tactic Notation "psatz" constr(dom) := xpsatz dom ltac:-1.

Ltac psatzl dom :=
  let tac := lazymatch dom with
  | Z => lia
  | Q =>
    psatzl_Q ;
    (* If csdp is not installed, the previous step might not produce any
    progress: the rest of the tactical will then fail. Hence the 'try'. *)
    try (abstract(intros __wit __varmap __ff ;
        change (Tauto.eval_f (Qeval_formula (@find Q 0%Q __varmap)) __ff) ;
        apply (QTautoChecker_sound __ff __wit); vm_cast_no_check (eq_refl true)))
  | R =>
    unfold Rdiv in * ; 
    psatzl_R ;
    (* If csdp is not installed, the previous step might not produce any
    progress: the rest of the tactical will then fail. Hence the 'try'. *)
    try abstract((intros __wit __varmap __ff ;
        change (Tauto.eval_f (Reval_formula (@find R 0%R __varmap)) __ff) ;
        apply (RTautoChecker_sound __ff __wit); vm_cast_no_check (eq_refl true)))
  | _ => fail "Unsupported domain"
  end in tac.


Ltac lra := 
  first [ psatzl R | psatzl Q ].



(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
