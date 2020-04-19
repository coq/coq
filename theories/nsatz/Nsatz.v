(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*
 Tactic nsatz: proofs of polynomials equalities in an integral domain
(commutative ring without zero divisor).

Examples: see test-suite/success/Nsatz.v

Reification is done using type classes, defined in Ncring_tac.v

*)

Require Import List.
Require Import Setoid.
Require Import BinPos.
Require Import BinList.
Require Import Znumtheory.
Require Export Morphisms Setoid Bool.
Require Export Algebra_syntax.
Require Export Ncring.
Require Export Ncring_initial.
Require Export Ncring_tac.
Require Export Integral_domain.
Require Import DiscrR.
Require Import ZArith.
Require Import Lia.

Require Export NsatzTactic.
(** Make use of [discrR] in [nsatz] *)
Ltac nsatz_internal_discrR ::= discrR.

(* Real numbers *)
Require Import Reals.
Require Import RealField.

Lemma Rsth : Setoid_Theory R (@eq R).
constructor;red;intros;subst;trivial.
Qed.

Instance Rops: (@Ring_ops R 0%R 1%R Rplus Rmult Rminus Ropp (@eq R)).
Defined.

Instance Rri : (Ring (Ro:=Rops)).
constructor;
try (try apply Rsth;
   try (unfold respectful, Proper; unfold equality; unfold eq_notation in *;
  intros; try rewrite H; try rewrite H0; reflexivity)).
 exact Rplus_0_l. exact Rplus_comm. symmetry. apply Rplus_assoc.
 exact Rmult_1_l.  exact Rmult_1_r. symmetry. apply Rmult_assoc.
 exact Rmult_plus_distr_r. intros; apply Rmult_plus_distr_l.
exact Rplus_opp_r.
Defined.

Class can_compute_Z (z : Z) := dummy_can_compute_Z : True.
Hint Extern 0 (can_compute_Z ?v) =>
  match isZcst v with true => exact I end : typeclass_instances.
Instance reify_IZR z lvar {_ : can_compute_Z z} : reify (PEc z) lvar (IZR z).
Defined.

Lemma R_one_zero: 1%R <> 0%R.
discrR.
Qed.

Instance Rcri: (Cring (Rr:=Rri)).
red. exact Rmult_comm. Defined.

Instance Rdi : (Integral_domain (Rcr:=Rcri)).
constructor.
exact Rmult_integral. exact R_one_zero. Defined.

(* Rational numbers *)
Require Import QArith.

Instance Qops: (@Ring_ops Q 0%Q 1%Q Qplus Qmult Qminus Qopp Qeq).
Defined.

Instance Qri : (Ring (Ro:=Qops)).
constructor.
try apply Q_Setoid.
apply Qplus_comp.
apply Qmult_comp.
apply Qminus_comp.
apply Qopp_comp.
 exact Qplus_0_l. exact Qplus_comm. apply Qplus_assoc.
 exact Qmult_1_l.  exact Qmult_1_r. apply Qmult_assoc.
 apply Qmult_plus_distr_l.  intros. apply Qmult_plus_distr_r.
reflexivity. exact Qplus_opp_r.
Defined.

Lemma Q_one_zero: not (Qeq 1%Q 0%Q).
Proof. unfold Qeq. simpl. lia.  Qed.

Instance Qcri: (Cring (Rr:=Qri)).
red. exact Qmult_comm. Defined.

Instance Qdi : (Integral_domain (Rcr:=Qcri)).
constructor.
exact Qmult_integral. exact Q_one_zero. Defined.

(* Integers *)
Lemma Z_one_zero: 1%Z <> 0%Z.
Proof. lia. Qed.

Instance Zcri: (Cring (Rr:=Zr)).
red. exact Z.mul_comm. Defined.

Instance Zdi : (Integral_domain (Rcr:=Zcri)).
constructor.
exact Zmult_integral. exact Z_one_zero. Defined.
