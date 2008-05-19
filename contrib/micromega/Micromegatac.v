(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
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
Require Export Ring_normalize.
Require Import ZArith.
Require Import Reals.
Require Export RingMicromega.
Require Import VarMap.
Require Tauto.

Ltac micromegac dom d :=
  let tac := lazymatch dom with
  | Z => 
    micromegap d ;
    intros __wit __varmap __ff ; 
    change (Tauto.eval_f (Zeval_formula (@find Z Z0 __varmap)) __ff) ; 
    apply (ZTautoChecker_sound __ff __wit); vm_compute ; reflexivity
  | R =>
    rmicromegap d ;
    intros __wit __varmap __ff ; 
    change (Tauto.eval_f (Reval_formula (@find R 0%R __varmap)) __ff) ; 
    apply (RTautoChecker_sound __ff __wit); vm_compute ; reflexivity
  | _ => fail "Unsupported domain"
  end in tac.

Tactic Notation "micromega" constr(dom) int_or_var(n) := micromegac dom n.
Tactic Notation "micromega" constr(dom) := micromegac dom ltac:-1.

Ltac zfarkas :=  omicronp ;
  intros __wit __varmap __ff ; 
  change (Tauto.eval_f (Zeval_formula (@find Z Z0 __varmap)) __ff) ; 
  apply (ZTautoChecker_sound __ff __wit); vm_compute ; reflexivity.

Ltac omicron dom :=
  let tac := lazymatch dom with
  | Z =>
    zomicronp ;
    intros __wit __varmap __ff ;
    change (Tauto.eval_f (Zeval_formula (@find Z Z0 __varmap)) __ff) ; 
    apply (ZTautoChecker_sound __ff __wit); vm_compute ; reflexivity
  | Q =>
    qomicronp ; 
    intros __wit __varmap __ff ; 
    change (Tauto.eval_f (Qeval_formula (@find Q 0%Q __varmap)) __ff) ; 
    apply (QTautoChecker_sound __ff __wit); vm_compute ; reflexivity
  | R => 
    romicronp ;
    intros __wit __varmap __ff ;
    change (Tauto.eval_f (Reval_formula (@find R 0%R __varmap)) __ff) ; 
    apply (RTautoChecker_sound __ff __wit); vm_compute ; reflexivity
  | _ => fail "Unsupported domain"
  end in tac.

Ltac sos dom :=
  let tac := lazymatch dom with
  | Z =>
    sosp ;
    intros __wit __varmap __ff ;
    change (Tauto.eval_f (Zeval_formula (@find Z Z0 __varmap)) __ff) ; 
    apply (ZTautoChecker_sound __ff __wit); vm_compute ; reflexivity
  | _ => fail "Unsupported domain"
  end in tac.


