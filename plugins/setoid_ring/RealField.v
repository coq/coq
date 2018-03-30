(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Nnat.
Require Import ArithRing.
Require Export Ring Field.
Require Import Rdefinitions.
Require Import Rpow_def.
Require Import Raxioms.

Local Open Scope R_scope.

Lemma RTheory : ring_theory 0 1 Rplus Rmult Rminus Ropp (eq (A:=R)).
Proof.
constructor.
 intro; apply Rplus_0_l.
 exact Rplus_comm.
 symmetry ; apply Rplus_assoc.
 intro; apply Rmult_1_l.
 exact Rmult_comm.
 symmetry ; apply Rmult_assoc.
 intros m n p.
   rewrite Rmult_comm.
   rewrite (Rmult_comm n p).
   rewrite (Rmult_comm m p).
   apply Rmult_plus_distr_l.
 reflexivity.
 exact Rplus_opp_r.
Qed.

Lemma Rfield : field_theory 0 1 Rplus Rmult Rminus Ropp Rdiv Rinv (eq(A:=R)).
Proof.
constructor.
 exact RTheory.
 exact R1_neq_R0.
 reflexivity.
 exact Rinv_l.
Qed.

Lemma Rlt_n_Sn : forall x, x < x + 1.
Proof.
intro.
elim archimed with x; intros.
destruct H0.
 apply Rlt_trans with (IZR (up x)); trivial.
    replace (IZR (up x)) with (x + (IZR (up x) - x))%R.
  apply Rplus_lt_compat_l; trivial.
  unfold Rminus.
    rewrite (Rplus_comm (IZR (up x)) (- x)).
    rewrite <- Rplus_assoc.
    rewrite Rplus_opp_r.
    apply Rplus_0_l.
 elim H0.
   unfold Rminus.
   rewrite (Rplus_comm (IZR (up x)) (- x)).
   rewrite <- Rplus_assoc.
   rewrite Rplus_opp_r.
   rewrite Rplus_0_l; trivial.
Qed.

Notation Rset := (Eqsth R).
Notation Rext := (Eq_ext Rplus Rmult Ropp).

Lemma Rlt_0_2 : 0 < 2.
Proof.
apply Rlt_trans with (0 + 1).
 apply Rlt_n_Sn.
 rewrite Rplus_comm.
   apply Rplus_lt_compat_l.
    replace R1 with (0 + 1).
  apply Rlt_n_Sn.
  apply Rplus_0_l.
Qed.

Lemma Rgen_phiPOS : forall x, InitialRing.gen_phiPOS1 1 Rplus Rmult x > 0.
unfold Rgt.
induction x; simpl; intros.
 apply Rlt_trans with (1 + 0).
  rewrite Rplus_comm.
    apply Rlt_n_Sn.
  apply Rplus_lt_compat_l.
    rewrite <- (Rmul_0_l Rset Rext RTheory 2).
    rewrite Rmult_comm.
    apply Rmult_lt_compat_l.
   apply Rlt_0_2.
   trivial.
 rewrite <- (Rmul_0_l Rset Rext RTheory 2).
   rewrite Rmult_comm.
   apply Rmult_lt_compat_l.
  apply Rlt_0_2.
  trivial.
  replace 1 with (0 + 1).
  apply Rlt_n_Sn.
  apply Rplus_0_l.
Qed.


Lemma Rgen_phiPOS_not_0 :
  forall x, InitialRing.gen_phiPOS1 1 Rplus Rmult x <> 0.
red; intros.
specialize (Rgen_phiPOS x).
rewrite H; intro.
apply (Rlt_asym 0 0); trivial.
Qed.

Lemma Zeq_bool_complete : forall x y,
  InitialRing.gen_phiZ 0%R 1%R Rplus Rmult Ropp x =
  InitialRing.gen_phiZ 0%R 1%R Rplus Rmult Ropp y ->
  Zeq_bool x y = true.
Proof gen_phiZ_complete Rset Rext Rfield Rgen_phiPOS_not_0.

Lemma Rdef_pow_add : forall (x:R) (n m:nat), pow x  (n + m) = pow x n * pow x m.
Proof.
  intros x n; elim n; simpl; auto with real.
  intros n0 H' m; rewrite H'; auto with real.
Qed.

Lemma R_power_theory : power_theory 1%R Rmult (@eq R) N.to_nat pow.
Proof.
 constructor. destruct n. reflexivity.
 simpl. induction p.
 - rewrite Pos2Nat.inj_xI. simpl. now rewrite plus_0_r, Rdef_pow_add, IHp.
 - rewrite Pos2Nat.inj_xO. simpl. now rewrite plus_0_r, Rdef_pow_add, IHp.
 - simpl. rewrite Rmult_comm;apply Rmult_1_l.
Qed.

Ltac Rpow_tac t :=
  match isnatcst t with
  | false => constr:(InitialRing.NotConstant)
  | _ => constr:(N.of_nat t)
  end.

Ltac IZR_tac t :=
  match t with
  | R0 => constr:(0%Z)
  | R1 => constr:(1%Z)
  | IZR ?u =>
    match isZcst u with
    | true => u
    | _ => constr:(InitialRing.NotConstant)
    end
  | _ => constr:(InitialRing.NotConstant)
  end.

Add Field RField : Rfield
   (completeness Zeq_bool_complete, constants [IZR_tac], power_tac R_power_theory [Rpow_tac]).
