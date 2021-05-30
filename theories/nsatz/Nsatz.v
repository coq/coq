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

#[global]
Instance Rops: (@Ring_ops R 0%R 1%R Rplus Rmult Rminus Ropp (@eq R)).
Defined.

#[global]
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
#[global]
Hint Extern 0 (can_compute_Z ?v) =>
  match isZcst v with true => exact I end : typeclass_instances.
#[global]
Instance reify_IZR z lvar {_ : can_compute_Z z} : reify (PEc z) lvar (IZR z).
Defined.

Lemma R_one_zero: 1%R <> 0%R.
discrR.
Qed.

#[global]
Instance Rcri: (Cring (Rr:=Rri)).
red. exact Rmult_comm. Defined.

#[global]
Instance Rdi : (Integral_domain (Rcr:=Rcri)).
constructor.
exact Rmult_integral. exact R_one_zero. Defined.
