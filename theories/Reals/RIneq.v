(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(************************************************************************)

(*********************************************************)
(** * Basic lemmas for the classical real numbers        *)
(*********************************************************)

Require Import ConstructiveRIneq.
Require Export Raxioms.
Require Import Rpow_def.
Require Import Zpower.
Require Export ZArithRing.
Require Import Omega.
Require Export RealField.

Local Open Scope Z_scope.
Local Open Scope R_scope.

Implicit Type r : R.

(*********************************************************)
(** ** Relation between orders and equality              *)
(*********************************************************)

(** Reflexivity of the large order *)

Lemma Rle_refl : forall r, r <= r.
Proof.
  intro; right; reflexivity.
Qed.
Hint Immediate Rle_refl: rorders.

Lemma Rge_refl : forall r, r <= r.
Proof. exact Rle_refl. Qed.
Hint Immediate Rge_refl: rorders.

(** Irreflexivity of the strict order *)

Lemma Rlt_irrefl : forall r, ~ r < r.
Proof.
  intros r H; eapply Rlt_asym; eauto.
Qed.
Hint Resolve Rlt_irrefl: real.

Lemma Rgt_irrefl : forall r, ~ r > r.
Proof. exact Rlt_irrefl. Qed.

Lemma Rlt_not_eq : forall r1 r2, r1 < r2 -> r1 <> r2.
Proof.
  red; intros r1 r2 H H0; apply (Rlt_irrefl r1).
  pattern r1 at 2; rewrite H0; trivial.
Qed.

Lemma Rgt_not_eq : forall r1 r2, r1 > r2 -> r1 <> r2.
Proof.
  intros; apply not_eq_sym; apply Rlt_not_eq; auto with real.
Qed.

(**********)
Lemma Rlt_dichotomy_converse : forall r1 r2, r1 < r2 \/ r1 > r2 -> r1 <> r2.
Proof.
  intuition.
  - apply Rlt_not_eq in H1. eauto.
  - apply Rgt_not_eq in H1. eauto.
Qed.
Hint Resolve Rlt_dichotomy_converse: real.

(** Reasoning by case on equality and order *)

(**********)
Lemma Req_dec : forall r1 r2, r1 = r2 \/ r1 <> r2.
Proof.
  intros; generalize (total_order_T r1 r2) Rlt_dichotomy_converse;
    unfold not; intuition eauto 3.
Qed.
Hint Resolve Req_dec: real.

(**********)
Lemma Rtotal_order : forall r1 r2, r1 < r2 \/ r1 = r2 \/ r1 > r2.
Proof.
  intros; generalize (total_order_T r1 r2); tauto.
Qed.

(**********)
Lemma Rdichotomy : forall r1 r2, r1 <> r2 -> r1 < r2 \/ r1 > r2.
Proof.
  intros; generalize (total_order_T r1 r2); tauto.
Qed.

(*********************************************************)
(** ** Relating [<], [>], [<=] and [>=]                  *)
(*********************************************************)

(*********************************************************)
(** ** Order                                             *)
(*********************************************************)

(** *** Relating strict and large orders *)

Lemma Rlt_le : forall r1 r2, r1 < r2 -> r1 <= r2.
Proof.
  intros; red; tauto.
Qed.
Hint Resolve Rlt_le: real.

Lemma Rgt_ge : forall r1 r2, r1 > r2 -> r1 >= r2.
Proof.
  intros; red; tauto.
Qed.

(**********)
Lemma Rle_ge : forall r1 r2, r1 <= r2 -> r2 >= r1.
Proof.
  destruct 1; red; auto with real.
Qed.
Hint Immediate Rle_ge: real.
Hint Resolve Rle_ge: rorders.

Lemma Rge_le : forall r1 r2, r1 >= r2 -> r2 <= r1.
Proof.
  destruct 1; red; auto with real.
Qed.
Hint Resolve Rge_le: real.
Hint Immediate Rge_le: rorders.

(**********)
Lemma Rlt_gt : forall r1 r2, r1 < r2 -> r2 > r1.
Proof.
  trivial.
Qed.
Hint Resolve Rlt_gt: rorders.

Lemma Rgt_lt : forall r1 r2, r1 > r2 -> r2 < r1.
Proof.
  trivial.
Qed.
Hint Immediate Rgt_lt: rorders.

(**********)

Lemma Rnot_le_lt : forall r1 r2, ~ r1 <= r2 -> r2 < r1.
Proof.
  intros r1 r2; generalize (Rtotal_order r1 r2); unfold Rle; tauto.
Qed.
Hint Immediate Rnot_le_lt: real.

Lemma Rnot_ge_gt : forall r1 r2, ~ r1 >= r2 -> r2 > r1.
Proof. intros; red; apply Rnot_le_lt. auto with real. Qed.

Lemma Rnot_le_gt : forall r1 r2, ~ r1 <= r2 -> r1 > r2.
Proof. intros; red; apply Rnot_le_lt. auto with real. Qed.

Lemma Rnot_ge_lt : forall r1 r2, ~ r1 >= r2 -> r1 < r2.
Proof. intros; apply Rnot_le_lt. auto with real. Qed.

Lemma Rnot_lt_le : forall r1 r2, ~ r1 < r2 -> r2 <= r1.
Proof.
  intros r1 r2 H; destruct (Rtotal_order r1 r2) as [ | [ H0 | H0 ] ].
    contradiction. subst; auto with rorders. auto with real.
Qed.

Lemma Rnot_gt_le : forall r1 r2, ~ r1 > r2 -> r1 <= r2.
Proof. auto using Rnot_lt_le with real. Qed.

Lemma Rnot_gt_ge : forall r1 r2, ~ r1 > r2 -> r2 >= r1.
Proof. intros; eauto using Rnot_lt_le with rorders. Qed.

Lemma Rnot_lt_ge : forall r1 r2, ~ r1 < r2 -> r1 >= r2.
Proof. eauto using Rnot_gt_ge with rorders. Qed.

(**********)
Lemma Rlt_not_le : forall r1 r2, r2 < r1 -> ~ r1 <= r2.
Proof.
  generalize Rlt_asym Rlt_dichotomy_converse; unfold Rle.
  unfold not; intuition eauto 3.
Qed.
Hint Immediate Rlt_not_le: real.

Lemma Rgt_not_le : forall r1 r2, r1 > r2 -> ~ r1 <= r2.
Proof. exact Rlt_not_le. Qed.

Lemma Rlt_not_ge : forall r1 r2, r1 < r2 -> ~ r1 >= r2.
Proof. red; intros; eapply Rlt_not_le; eauto with real. Qed.
Hint Immediate Rlt_not_ge: real.

Lemma Rgt_not_ge : forall r1 r2, r2 > r1 -> ~ r1 >= r2.
Proof. exact Rlt_not_ge. Qed.

Lemma Rle_not_lt : forall r1 r2, r2 <= r1 -> ~ r1 < r2.
Proof.
  intros r1 r2. generalize (Rlt_asym r1 r2) (Rlt_dichotomy_converse r1 r2).
  unfold Rle; intuition.
Qed.

Lemma Rge_not_lt : forall r1 r2, r1 >= r2 -> ~ r1 < r2.
Proof. intros; apply Rle_not_lt; auto with real. Qed.

Lemma Rle_not_gt : forall r1 r2, r1 <= r2 -> ~ r1 > r2.
Proof. do 2 intro; apply Rle_not_lt. Qed.

Lemma Rge_not_gt : forall r1 r2, r2 >= r1 -> ~ r1 > r2.
Proof. do 2 intro; apply Rge_not_lt. Qed.

(**********)
Lemma Req_le : forall r1 r2, r1 = r2 -> r1 <= r2.
Proof.
  unfold Rle; tauto.
Qed.
Hint Immediate Req_le: real.

Lemma Req_ge : forall r1 r2, r1 = r2 -> r1 >= r2.
Proof.
  unfold Rge; tauto.
Qed.
Hint Immediate Req_ge: real.

Lemma Req_le_sym : forall r1 r2, r2 = r1 -> r1 <= r2.
Proof.
  unfold Rle; auto.
Qed.
Hint Immediate Req_le_sym: real.

Lemma Req_ge_sym : forall r1 r2, r2 = r1 -> r1 >= r2.
Proof.
  unfold Rge; auto.
Qed.
Hint Immediate Req_ge_sym: real.

(** *** Asymmetry *)

(** Remark: [Rlt_asym] is an axiom *)

Lemma Rgt_asym : forall r1 r2:R, r1 > r2 -> ~ r2 > r1.
Proof. do 2 intro; apply Rlt_asym. Qed.

(** *** Antisymmetry *)

Lemma Rle_antisym : forall r1 r2, r1 <= r2 -> r2 <= r1 -> r1 = r2.
Proof.
  intros r1 r2; generalize (Rlt_asym r1 r2); unfold Rle; intuition.
Qed.
Hint Resolve Rle_antisym: real.

Lemma Rge_antisym : forall r1 r2, r1 >= r2 -> r2 >= r1 -> r1 = r2.
Proof. auto with real. Qed.

(**********)
Lemma Rle_le_eq : forall r1 r2, r1 <= r2 /\ r2 <= r1 <-> r1 = r2.
Proof.
  intuition.
Qed.

Lemma Rge_ge_eq : forall r1 r2, r1 >= r2 /\ r2 >= r1 <-> r1 = r2.
Proof.
  intuition.
Qed.

(** *** Compatibility with equality *)

Lemma Rlt_eq_compat :
  forall r1 r2 r3 r4, r1 = r2 -> r2 < r4 -> r4 = r3 -> r1 < r3.
Proof.
  intros x x' y y'; intros; replace x with x'; replace y with y'; assumption.
Qed.

Lemma Rgt_eq_compat :
  forall r1 r2 r3 r4, r1 = r2 -> r2 > r4 -> r4 = r3 -> r1 > r3.
Proof. intros; red; apply Rlt_eq_compat with (r2:=r4) (r4:=r2); auto. Qed.

(** *** Transitivity *)

(** Remark: [Rlt_trans] is an axiom *)

Lemma Rle_trans : forall r1 r2 r3, r1 <= r2 -> r2 <= r3 -> r1 <= r3.
Proof.
  generalize eq_trans Rlt_trans Rlt_eq_compat.
  unfold Rle.
  intuition eauto 2.
Qed.

Lemma Rge_trans : forall r1 r2 r3, r1 >= r2 -> r2 >= r3 -> r1 >= r3.
Proof. eauto using Rle_trans with rorders. Qed.

Lemma Rgt_trans : forall r1 r2 r3, r1 > r2 -> r2 > r3 -> r1 > r3.
Proof. eauto using Rlt_trans with rorders. Qed.

(**********)
Lemma Rle_lt_trans : forall r1 r2 r3, r1 <= r2 -> r2 < r3 -> r1 < r3.
Proof.
  generalize Rlt_trans Rlt_eq_compat.
  unfold Rle.
  intuition eauto 2.
Qed.

Lemma Rlt_le_trans : forall r1 r2 r3, r1 < r2 -> r2 <= r3 -> r1 < r3.
Proof.
  generalize Rlt_trans Rlt_eq_compat; unfold Rle; intuition eauto 2.
Qed.

Lemma Rge_gt_trans : forall r1 r2 r3, r1 >= r2 -> r2 > r3 -> r1 > r3.
Proof. eauto using Rlt_le_trans with rorders. Qed.

Lemma Rgt_ge_trans : forall r1 r2 r3, r1 > r2 -> r2 >= r3 -> r1 > r3.
Proof. eauto using Rle_lt_trans with rorders. Qed.

(** *** (Classical) decidability *)

Lemma Rlt_dec : forall r1 r2, {r1 < r2} + {~ r1 < r2}.
Proof.
  intros; generalize (total_order_T r1 r2) (Rlt_dichotomy_converse r1 r2);
    intuition.
Qed.

Lemma Rle_dec : forall r1 r2, {r1 <= r2} + {~ r1 <= r2}.
Proof.
  intros r1 r2.
  generalize (total_order_T r1 r2) (Rlt_dichotomy_converse r1 r2).
  intuition eauto 4 with real.
Qed.

Lemma Rgt_dec : forall r1 r2, {r1 > r2} + {~ r1 > r2}.
Proof. do 2 intro; apply Rlt_dec. Qed.

Lemma Rge_dec : forall r1 r2, {r1 >= r2} + {~ r1 >= r2}.
Proof. intros; edestruct Rle_dec; [left|right]; eauto with rorders. Qed.

Lemma Rlt_le_dec : forall r1 r2, {r1 < r2} + {r2 <= r1}.
Proof.
  intros; generalize (total_order_T r1 r2); intuition.
Qed.

Lemma Rgt_ge_dec : forall r1 r2, {r1 > r2} + {r2 >= r1}.
Proof. intros; edestruct Rlt_le_dec; [left|right]; eauto with rorders. Qed.

Lemma Rle_lt_dec : forall r1 r2, {r1 <= r2} + {r2 < r1}.
Proof.
  intros; generalize (total_order_T r1 r2); intuition.
Qed.

Lemma Rge_gt_dec : forall r1 r2, {r1 >= r2} + {r2 > r1}.
Proof. intros; edestruct Rle_lt_dec; [left|right]; eauto with rorders. Qed.

Lemma Rlt_or_le : forall r1 r2, r1 < r2 \/ r2 <= r1.
Proof.
  intros n m; elim (Rle_lt_dec m n); auto with real.
Qed.

Lemma Rgt_or_ge : forall r1 r2, r1 > r2 \/ r2 >= r1.
Proof. intros; edestruct Rlt_or_le; [left|right]; eauto with rorders. Qed.

Lemma Rle_or_lt : forall r1 r2, r1 <= r2 \/ r2 < r1.
Proof.
  intros n m; elim (Rlt_le_dec m n); auto with real.
Qed.

Lemma Rge_or_gt : forall r1 r2, r1 >= r2 \/ r2 > r1.
Proof. intros; edestruct Rle_or_lt; [left|right]; eauto with rorders. Qed.

Lemma Rle_lt_or_eq_dec : forall r1 r2, r1 <= r2 -> {r1 < r2} + {r1 = r2}.
Proof.
  intros r1 r2 H; generalize (total_order_T r1 r2); intuition.
Qed.

(**********)
Lemma inser_trans_R :
  forall r1 r2 r3 r4, r1 <= r2 < r3 -> {r1 <= r2 < r4} + {r4 <= r2 < r3}.
Proof.
  intros n m p q; intros; generalize (Rlt_le_dec m q); intuition.
Qed.

(*********************************************************)
(** ** Addition                                          *)
(*********************************************************)

(** Remark: [Rplus_0_l] is an axiom *)

Lemma Rplus_0_r : forall r, r + 0 = r.
Proof.
  intro; ring.
Qed.
Hint Resolve Rplus_0_r: real.

Lemma Rplus_ne : forall r, r + 0 = r /\ 0 + r = r.
Proof.
  split; ring.
Qed.
Hint Resolve Rplus_ne: real.

(**********)

(** Remark: [Rplus_opp_r] is an axiom *)

Lemma Rplus_opp_l : forall r, - r + r = 0.
Proof.
  intro; ring.
Qed.
Hint Resolve Rplus_opp_l: real.

(**********)
Lemma Rplus_opp_r_uniq : forall r1 r2, r1 + r2 = 0 -> r2 = - r1.
Proof.
  intros x y H;
    replace y with (- x + x + y) by ring.
  rewrite Rplus_assoc; rewrite H; ring.
Qed.

Definition f_equal_R := (f_equal (A:=R)).

Hint Resolve f_equal_R : real.

Lemma Rplus_eq_compat_l : forall r r1 r2, r1 = r2 -> r + r1 = r + r2.
Proof.
  intros r r1 r2.
  apply f_equal.
Qed.

Lemma Rplus_eq_compat_r : forall r r1 r2, r1 = r2 -> r1 + r = r2 + r.
Proof.
  intros r r1 r2.
  apply (f_equal (fun v => v + r)).
Qed.


(**********)
Lemma Rplus_eq_reg_l : forall r r1 r2, r + r1 = r + r2 -> r1 = r2.
Proof.
  intros; transitivity (- r + r + r1).
  ring.
  transitivity (- r + r + r2).
  repeat rewrite Rplus_assoc; rewrite <- H; reflexivity.
  ring.
Qed.
Hint Resolve Rplus_eq_reg_l: real.

Lemma Rplus_eq_reg_r : forall r r1 r2, r1 + r = r2 + r -> r1 = r2.
Proof.
  intros r r1 r2 H.
  apply Rplus_eq_reg_l with r.
  now rewrite 2!(Rplus_comm r).
Qed.

(**********)
Lemma Rplus_0_r_uniq : forall r r1, r + r1 = r -> r1 = 0.
Proof.
  intros r b; pattern r at 2; replace r with (r + 0); eauto with real.
Qed.

(***********)
Lemma Rplus_eq_0_l :
  forall r1 r2, 0 <= r1 -> 0 <= r2 -> r1 + r2 = 0 -> r1 = 0.
Proof.
  intros. apply Rquot1. rewrite Rrepr_0.
  apply (Rplus_eq_0_l (Rrepr r1) (Rrepr r2)).
  rewrite Rrepr_le, Rrepr_0 in H. exact H.
  rewrite Rrepr_le, Rrepr_0 in H0. exact H0.
  rewrite <- Rrepr_plus, H1, Rrepr_0. reflexivity.
Qed.

Lemma Rplus_eq_R0 :
  forall r1 r2, 0 <= r1 -> 0 <= r2 -> r1 + r2 = 0 -> r1 = 0 /\ r2 = 0.
Proof.
  intros a b; split.
  apply Rplus_eq_0_l with b; auto with real.
  apply Rplus_eq_0_l with a; auto with real.
  rewrite Rplus_comm; auto with real.
Qed.

(*********************************************************)
(** ** Multiplication                                    *)
(*********************************************************)

(**********)
Lemma Rinv_r : forall r, r <> 0 -> r * / r = 1.
Proof.
  intros; field; trivial.
Qed.
Hint Resolve Rinv_r: real.

Lemma Rinv_l_sym : forall r, r <> 0 -> 1 = / r * r.
Proof.
  intros; field; trivial.
Qed.
Hint Resolve Rinv_l_sym: real.

Lemma Rinv_r_sym : forall r, r <> 0 -> 1 = r * / r.
Proof.
  intros; field; trivial.
Qed.
Hint Resolve Rinv_r_sym: real.

(**********)
Lemma Rmult_0_r : forall r, r * 0 = 0.
Proof.
  intro; ring.
Qed.
Hint Resolve Rmult_0_r: real.

(**********)
Lemma Rmult_0_l : forall r, 0 * r = 0.
Proof.
  intro; ring.
Qed.
Hint Resolve Rmult_0_l: real.

(**********)
Lemma Rmult_ne : forall r, r * 1 = r /\ 1 * r = r.
Proof.
  intro; split; ring.
Qed.
Hint Resolve Rmult_ne: real.

(**********)
Lemma Rmult_1_r : forall r, r * 1 = r.
Proof.
  intro; ring.
Qed.
Hint Resolve Rmult_1_r: real.

(**********)
Lemma Rmult_eq_compat_l : forall r r1 r2, r1 = r2 -> r * r1 = r * r2.
Proof.
  auto with real.
Qed.


Lemma Rmult_eq_compat_r : forall r r1 r2, r1 = r2 -> r1 * r = r2 * r.
Proof.
  intros.
  rewrite <- 2!(Rmult_comm r).
  now apply Rmult_eq_compat_l.
Qed.

(**********)
Lemma Rmult_eq_reg_l : forall r r1 r2, r * r1 = r * r2 -> r <> 0 -> r1 = r2.
Proof.
  intros. apply Rquot1. apply (Rmult_eq_reg_l (Rrepr r)).
  rewrite <- Rrepr_mult, <- Rrepr_mult, H. reflexivity.
  rewrite Rrepr_appart, Rrepr_0 in H0. exact H0.
Qed.

Lemma Rmult_eq_reg_r : forall r r1 r2, r1 * r = r2 * r -> r <> 0 -> r1 = r2.
Proof.
  intros.
  apply Rmult_eq_reg_l with (2 := H0).
  now rewrite 2!(Rmult_comm r).
Qed.

(**********)
Lemma Rmult_integral : forall r1 r2, r1 * r2 = 0 -> r1 = 0 \/ r2 = 0.
Proof.
  intros; case (Req_dec r1 0); [ intro Hz | intro Hnotz ].
  auto.
  right; apply Rmult_eq_reg_l with r1; trivial.
  rewrite H; auto with real.
Qed.

(**********)
Lemma Rmult_eq_0_compat : forall r1 r2, r1 = 0 \/ r2 = 0 -> r1 * r2 = 0.
Proof.
  intros r1 r2 [H| H]; rewrite H; auto with real.
Qed.

Hint Resolve Rmult_eq_0_compat: real.

(**********)
Lemma Rmult_eq_0_compat_r : forall r1 r2, r1 = 0 -> r1 * r2 = 0.
Proof.
  auto with real.
Qed.

(**********)
Lemma Rmult_eq_0_compat_l : forall r1 r2, r2 = 0 -> r1 * r2 = 0.
Proof.
  auto with real.
Qed.

(**********)
Lemma Rmult_neq_0_reg : forall r1 r2, r1 * r2 <> 0 -> r1 <> 0 /\ r2 <> 0.
Proof.
  intros r1 r2 H; split; red; intro; apply H; auto with real.
Qed.

(**********)
Lemma Rmult_integral_contrapositive :
  forall r1 r2, r1 <> 0 /\ r2 <> 0 -> r1 * r2 <> 0.
Proof.
  red; intros r1 r2 [H1 H2] H.
  case (Rmult_integral r1 r2); auto with real.
Qed.
Hint Resolve Rmult_integral_contrapositive: real.

Lemma Rmult_integral_contrapositive_currified :
  forall r1 r2, r1 <> 0 -> r2 <> 0 -> r1 * r2 <> 0.
Proof. auto using Rmult_integral_contrapositive. Qed.

(**********)
Lemma Rmult_plus_distr_r :
  forall r1 r2 r3, (r1 + r2) * r3 = r1 * r3 + r2 * r3.
Proof.
  intros; ring.
Qed.

(*********************************************************)
(** ** Square function                                   *)
(*********************************************************)

(***********)
Definition Rsqr r : R := r * r.

Notation "r ²" := (Rsqr r) (at level 1, format "r ²") : R_scope.

(***********)
Lemma Rsqr_0 : Rsqr 0 = 0.
  unfold Rsqr; auto with real.
Qed.

(***********)
Lemma Rsqr_0_uniq : forall r, Rsqr r = 0 -> r = 0.
  unfold Rsqr; intros; elim (Rmult_integral r r H); trivial.
Qed.

(*********************************************************)
(** ** Opposite                                          *)
(*********************************************************)

(**********)
Lemma Ropp_eq_compat : forall r1 r2, r1 = r2 -> - r1 = - r2.
Proof.
  auto with real.
Qed.
Hint Resolve Ropp_eq_compat: real.

(**********)
Lemma Ropp_0 : -0 = 0.
Proof.
  ring.
Qed.
Hint Resolve Ropp_0: real.

(**********)
Lemma Ropp_eq_0_compat : forall r, r = 0 -> - r = 0.
Proof.
  intros; rewrite H; auto with real.
Qed.
Hint Resolve Ropp_eq_0_compat: real.

(**********)
Lemma Ropp_involutive : forall r, - - r = r.
Proof.
  intro; ring.
Qed.
Hint Resolve Ropp_involutive: real.

(*********)
Lemma Ropp_neq_0_compat : forall r, r <> 0 -> - r <> 0.
Proof.
  red; intros r H H0.
  apply H.
  transitivity (- - r); auto with real.
Qed.
Hint Resolve Ropp_neq_0_compat: real.

(**********)
Lemma Ropp_plus_distr : forall r1 r2, - (r1 + r2) = - r1 + - r2.
Proof.
  intros; ring.
Qed.
Hint Resolve Ropp_plus_distr: real.

(*********************************************************)
(** ** Opposite and multiplication                       *)
(*********************************************************)

Lemma Ropp_mult_distr_l : forall r1 r2, - (r1 * r2) = - r1 * r2.
Proof.
  intros; ring.
Qed.

Lemma Ropp_mult_distr_l_reverse : forall r1 r2, - r1 * r2 = - (r1 * r2).
Proof.
  intros; ring.
Qed.
Hint Resolve Ropp_mult_distr_l_reverse: real.

(**********)
Lemma Rmult_opp_opp : forall r1 r2, - r1 * - r2 = r1 * r2.
Proof.
  intros; ring.
Qed.
Hint Resolve Rmult_opp_opp: real.

Lemma Ropp_mult_distr_r : forall r1 r2, - (r1 * r2) = r1 * - r2.
Proof.
  intros; ring.
Qed.

Lemma Ropp_mult_distr_r_reverse : forall r1 r2, r1 * - r2 = - (r1 * r2).
Proof.
  intros; ring.
Qed.

(*********************************************************)
(** ** Subtraction                                       *)
(*********************************************************)

Lemma Rminus_0_r : forall r, r - 0 = r.
Proof.
  intro; ring.
Qed.
Hint Resolve Rminus_0_r: real.

Lemma Rminus_0_l : forall r, 0 - r = - r.
Proof.
  intro; ring.
Qed.
Hint Resolve Rminus_0_l: real.

(**********)
Lemma Ropp_minus_distr : forall r1 r2, - (r1 - r2) = r2 - r1.
Proof.
  intros; ring.
Qed.
Hint Resolve Ropp_minus_distr: real.

Lemma Ropp_minus_distr' : forall r1 r2, - (r2 - r1) = r1 - r2.
Proof.
  intros; ring.
Qed.

(**********)
Lemma Rminus_diag_eq : forall r1 r2, r1 = r2 -> r1 - r2 = 0.
Proof.
  intros; rewrite H; ring.
Qed.
Hint Resolve Rminus_diag_eq: real.

(**********)
Lemma Rminus_diag_uniq : forall r1 r2, r1 - r2 = 0 -> r1 = r2.
Proof.
  intros r1 r2; unfold Rminus; rewrite Rplus_comm; intro.
  rewrite <- (Ropp_involutive r2); apply (Rplus_opp_r_uniq (- r2) r1 H).
Qed.
Hint Immediate Rminus_diag_uniq: real.

Lemma Rminus_diag_uniq_sym : forall r1 r2, r2 - r1 = 0 -> r1 = r2.
Proof.
  intros; generalize (Rminus_diag_uniq r2 r1 H); clear H; intro H; rewrite H;
    ring.
Qed.
Hint Immediate Rminus_diag_uniq_sym: real.

Lemma Rplus_minus : forall r1 r2, r1 + (r2 - r1) = r2.
Proof.
  intros; ring.
Qed.
Hint Resolve Rplus_minus: real.

(**********)
Lemma Rminus_eq_contra : forall r1 r2, r1 <> r2 -> r1 - r2 <> 0.
Proof.
  red; intros r1 r2 H H0.
  apply H; auto with real.
Qed.
Hint Resolve Rminus_eq_contra: real.

Lemma Rminus_not_eq : forall r1 r2, r1 - r2 <> 0 -> r1 <> r2.
Proof.
  red; intros; elim H; apply Rminus_diag_eq; auto.
Qed.
Hint Resolve Rminus_not_eq: real.

Lemma Rminus_not_eq_right : forall r1 r2, r2 - r1 <> 0 -> r1 <> r2.
Proof.
  red; intros; elim H; rewrite H0; ring.
Qed.
Hint Resolve Rminus_not_eq_right: real.

(**********)
Lemma Rmult_minus_distr_l :
  forall r1 r2 r3, r1 * (r2 - r3) = r1 * r2 - r1 * r3.
Proof.
  intros; ring.
Qed.

(*********************************************************)
(** ** Inverse                                           *)
(*********************************************************)

Lemma Rinv_1 : / 1 = 1.
Proof.
  field.
Qed.
Hint Resolve Rinv_1: real.

(*********)
Lemma Rinv_neq_0_compat : forall r, r <> 0 -> / r <> 0.
Proof.
  red; intros; apply R1_neq_R0.
  replace 1 with (/ r * r); auto with real.
Qed.
Hint Resolve Rinv_neq_0_compat: real.

(*********)
Lemma Rinv_involutive : forall r, r <> 0 -> / / r = r.
Proof.
  intros; field; trivial.
Qed.
Hint Resolve Rinv_involutive: real.

(*********)
Lemma Rinv_mult_distr :
  forall r1 r2, r1 <> 0 -> r2 <> 0 -> / (r1 * r2) = / r1 * / r2.
Proof.
  intros; field; auto.  
Qed.

(*********)
Lemma Ropp_inv_permute : forall r, r <> 0 -> - / r = / - r.
Proof.
  intros; field; trivial.
Qed.

Lemma Rinv_r_simpl_r : forall r1 r2, r1 <> 0 -> r1 * / r1 * r2 = r2.
Proof.
  intros; transitivity (1 * r2); auto with real.
  rewrite Rinv_r; auto with real.
Qed.

Lemma Rinv_r_simpl_l : forall r1 r2, r1 <> 0 -> r2 * r1 * / r1 = r2.
Proof.
  intros; transitivity (r2 * 1); auto with real.
  transitivity (r2 * (r1 * / r1)); auto with real.
Qed.

Lemma Rinv_r_simpl_m : forall r1 r2, r1 <> 0 -> r1 * r2 * / r1 = r2.
Proof.
  intros; transitivity (r2 * 1); auto with real.
  transitivity (r2 * (r1 * / r1)); auto with real.
  ring.
Qed.
Hint Resolve Rinv_r_simpl_l Rinv_r_simpl_r Rinv_r_simpl_m: real.

(*********)
Lemma Rinv_mult_simpl :
  forall r1 r2 r3, r1 <> 0 -> r1 * / r2 * (r3 * / r1) = r3 * / r2.
Proof.
  intros a b c; intros.
  transitivity (a * / a * (c * / b)); auto with real.
  ring.
Qed.

(*********************************************************)
(** ** Order and addition                                *)
(*********************************************************)

(** *** Compatibility *)

(** Remark: [Rplus_lt_compat_l] is an axiom *)

Lemma Rplus_gt_compat_l : forall r r1 r2, r1 > r2 -> r + r1 > r + r2.
Proof. eauto using Rplus_lt_compat_l with rorders. Qed.
Hint Resolve Rplus_gt_compat_l: real.

(**********)
Lemma Rplus_lt_compat_r : forall r r1 r2, r1 < r2 -> r1 + r < r2 + r.
Proof.
  intros.
  rewrite (Rplus_comm r1 r); rewrite (Rplus_comm r2 r); auto with real.
Qed.
Hint Resolve Rplus_lt_compat_r: real.

Lemma Rplus_gt_compat_r : forall r r1 r2, r1 > r2 -> r1 + r > r2 + r.
Proof. do 3 intro; apply Rplus_lt_compat_r. Qed.

(**********)
Lemma Rplus_le_compat_l : forall r r1 r2, r1 <= r2 -> r + r1 <= r + r2.
Proof.
  unfold Rle; intros; elim H; intro.
  left; apply (Rplus_lt_compat_l r r1 r2 H0).
  right; rewrite <- H0; auto with zarith real.
Qed.

Lemma Rplus_ge_compat_l : forall r r1 r2, r1 >= r2 -> r + r1 >= r + r2.
Proof. auto using Rplus_le_compat_l with rorders. Qed.
Hint Resolve Rplus_ge_compat_l: real.

(**********)
Lemma Rplus_le_compat_r : forall r r1 r2, r1 <= r2 -> r1 + r <= r2 + r.
Proof.
  unfold Rle; intros; elim H; intro.
  left; apply (Rplus_lt_compat_r r r1 r2 H0).
  right; rewrite <- H0; auto with real.
Qed.

Hint Resolve Rplus_le_compat_l Rplus_le_compat_r: real.

Lemma Rplus_ge_compat_r : forall r r1 r2, r1 >= r2 -> r1 + r >= r2 + r.
Proof. auto using Rplus_le_compat_r with rorders. Qed.

(*********)
Lemma Rplus_lt_compat :
  forall r1 r2 r3 r4, r1 < r2 -> r3 < r4 -> r1 + r3 < r2 + r4.
Proof.
  intros; apply Rlt_trans with (r2 + r3); auto with real.
Qed.
Hint Immediate Rplus_lt_compat: real.

Lemma Rplus_le_compat :
  forall r1 r2 r3 r4, r1 <= r2 -> r3 <= r4 -> r1 + r3 <= r2 + r4.
Proof.
  intros; apply Rle_trans with (r2 + r3); auto with real.
Qed.
Hint Immediate Rplus_le_compat: real.

Lemma Rplus_gt_compat :
  forall r1 r2 r3 r4, r1 > r2 -> r3 > r4 -> r1 + r3 > r2 + r4.
Proof. auto using Rplus_lt_compat with rorders. Qed.

Lemma Rplus_ge_compat :
  forall r1 r2 r3 r4, r1 >= r2 -> r3 >= r4 -> r1 + r3 >= r2 + r4.
Proof. auto using Rplus_le_compat with rorders. Qed.

(*********)
Lemma Rplus_lt_le_compat :
  forall r1 r2 r3 r4, r1 < r2 -> r3 <= r4 -> r1 + r3 < r2 + r4.
Proof.
  intros; apply Rlt_le_trans with (r2 + r3); auto with real.
Qed.

Lemma Rplus_le_lt_compat :
  forall r1 r2 r3 r4, r1 <= r2 -> r3 < r4 -> r1 + r3 < r2 + r4.
Proof.
  intros; apply Rle_lt_trans with (r2 + r3); auto with real.
Qed.

Hint Immediate Rplus_lt_le_compat Rplus_le_lt_compat: real.

Lemma Rplus_gt_ge_compat :
  forall r1 r2 r3 r4, r1 > r2 -> r3 >= r4 -> r1 + r3 > r2 + r4.
Proof. auto using Rplus_lt_le_compat with rorders. Qed.

Lemma Rplus_ge_gt_compat :
  forall r1 r2 r3 r4, r1 >= r2 -> r3 > r4 -> r1 + r3 > r2 + r4.
Proof. auto using Rplus_le_lt_compat with rorders. Qed.

(**********)
Lemma Rplus_lt_0_compat : forall r1 r2, 0 < r1 -> 0 < r2 -> 0 < r1 + r2.
Proof.
  intros x y; intros; apply Rlt_trans with x;
    [ assumption
      | pattern x at 1; rewrite <- (Rplus_0_r x); apply Rplus_lt_compat_l;
        assumption ].
Qed.

Lemma Rplus_le_lt_0_compat : forall r1 r2, 0 <= r1 -> 0 < r2 -> 0 < r1 + r2.
Proof.
  intros x y; intros; apply Rle_lt_trans with x;
    [ assumption
      | pattern x at 1; rewrite <- (Rplus_0_r x); apply Rplus_lt_compat_l;
        assumption ].
Qed.

Lemma Rplus_lt_le_0_compat : forall r1 r2, 0 < r1 -> 0 <= r2 -> 0 < r1 + r2.
Proof.
  intros x y; intros; rewrite <- Rplus_comm; apply Rplus_le_lt_0_compat;
    assumption.
Qed.

Lemma Rplus_le_le_0_compat : forall r1 r2, 0 <= r1 -> 0 <= r2 -> 0 <= r1 + r2.
Proof.
  intros x y; intros; apply Rle_trans with x;
    [ assumption
      | pattern x at 1; rewrite <- (Rplus_0_r x); apply Rplus_le_compat_l;
        assumption ].
Qed.

(**********)
Lemma sum_inequa_Rle_lt :
  forall a x b c y d:R,
    a <= x -> x < b -> c < y -> y <= d -> a + c < x + y < b + d.
Proof.
  intros; split.
  apply Rlt_le_trans with (a + y); auto with real.
  apply Rlt_le_trans with (b + y); auto with real.
Qed.

(** *** Cancellation *)

Lemma Rplus_lt_reg_l : forall r r1 r2, r + r1 < r + r2 -> r1 < r2.
Proof.
  intros. rewrite Rlt_def. apply (Rplus_lt_reg_l (Rrepr r)).
  rewrite <- Rrepr_plus, <- Rrepr_plus.
  rewrite Rlt_def in H. exact H.
Qed.

Lemma Rplus_lt_reg_r : forall r r1 r2, r1 + r < r2 + r -> r1 < r2.
Proof.
  intros. rewrite Rlt_def. apply (Rplus_lt_reg_r (Rrepr r)).
  rewrite <- Rrepr_plus, <- Rrepr_plus. rewrite Rlt_def in H. exact H.
Qed.

Lemma Rplus_le_reg_l : forall r r1 r2, r + r1 <= r + r2 -> r1 <= r2.
Proof.
  unfold Rle; intros; elim H; intro.
  left; apply (Rplus_lt_reg_l r r1 r2 H0).
  right; apply (Rplus_eq_reg_l r r1 r2 H0).
Qed.

Lemma Rplus_le_reg_r : forall r r1 r2, r1 + r <= r2 + r -> r1 <= r2.
Proof.
  intros.
  apply (Rplus_le_reg_l r).
  now rewrite 2!(Rplus_comm r).
Qed.

Lemma Rplus_gt_reg_l : forall r r1 r2, r + r1 > r + r2 -> r1 > r2.
Proof.
  unfold Rgt; intros; apply (Rplus_lt_reg_l r r2 r1 H).
Qed.

Lemma Rplus_ge_reg_l : forall r r1 r2, r + r1 >= r + r2 -> r1 >= r2.
Proof.
  intros; apply Rle_ge; apply Rplus_le_reg_l with r; auto with real.
Qed.

(**********)
Lemma Rplus_le_reg_pos_r :
  forall r1 r2 r3, 0 <= r2 -> r1 + r2 <= r3 -> r1 <= r3.
Proof.
  intros x y z; intros; apply Rle_trans with (x + y);
    [ pattern x at 1; rewrite <- (Rplus_0_r x); apply Rplus_le_compat_l;
      assumption
      | assumption ].
Qed.

Lemma Rplus_lt_reg_pos_r : forall r1 r2 r3, 0 <= r2 -> r1 + r2 < r3 -> r1 < r3.
Proof.
  intros x y z; intros; apply Rle_lt_trans with (x + y);
    [ pattern x at 1; rewrite <- (Rplus_0_r x); apply Rplus_le_compat_l;
      assumption
      | assumption ].
Qed.

Lemma Rplus_ge_reg_neg_r :
  forall r1 r2 r3, 0 >= r2 -> r1 + r2 >= r3 -> r1 >= r3.
Proof.
  intros x y z; intros; apply Rge_trans with (x + y);
    [ pattern x at 1; rewrite <- (Rplus_0_r x); apply Rplus_ge_compat_l;
      assumption
      | assumption ].
Qed.

Lemma Rplus_gt_reg_neg_r : forall r1 r2 r3, 0 >= r2 -> r1 + r2 > r3 -> r1 > r3.
Proof.
  intros x y z; intros; apply Rge_gt_trans with (x + y);
    [ pattern x at 1; rewrite <- (Rplus_0_r x); apply Rplus_ge_compat_l;
      assumption
      | assumption ].
Qed.

(*********************************************************)
(** ** Order and opposite                                *)
(*********************************************************)

(** *** Contravariant compatibility *)

Lemma Ropp_gt_lt_contravar : forall r1 r2, r1 > r2 -> - r1 < - r2.
Proof.
  intros. rewrite Rlt_def. rewrite Rrepr_opp, Rrepr_opp.
  apply Ropp_gt_lt_contravar. unfold Rgt in H.
  rewrite Rlt_def in H. exact H.
Qed.
Hint Resolve Ropp_gt_lt_contravar : core.

Lemma Ropp_lt_gt_contravar : forall r1 r2, r1 < r2 -> - r1 > - r2.
Proof.
  intros. unfold Rgt. rewrite Rlt_def. rewrite Rrepr_opp, Rrepr_opp.
  apply Ropp_lt_gt_contravar. rewrite Rlt_def in H. exact H.
Qed.
Hint Resolve Ropp_lt_gt_contravar: real.

(**********)
Lemma Ropp_lt_contravar : forall r1 r2, r2 < r1 -> - r1 < - r2.
Proof.
  auto with real.
Qed.
Hint Resolve Ropp_lt_contravar: real.

Lemma Ropp_gt_contravar : forall r1 r2, r2 > r1 -> - r1 > - r2.
Proof. auto with real. Qed.

(**********)
Lemma Ropp_le_ge_contravar : forall r1 r2, r1 <= r2 -> - r1 >= - r2.
Proof.
  unfold Rge; intros r1 r2 [H| H]; auto with real.
Qed.
Hint Resolve Ropp_le_ge_contravar: real.

Lemma Ropp_ge_le_contravar : forall r1 r2, r1 >= r2 -> - r1 <= - r2.
Proof.
  unfold Rle; intros r1 r2 [H| H]; auto with real.
Qed.
Hint Resolve Ropp_ge_le_contravar: real.

(**********)
Lemma Ropp_le_contravar : forall r1 r2, r2 <= r1 -> - r1 <= - r2.
Proof.
  intros r1 r2 H; elim H; auto with real.
Qed.
Hint Resolve Ropp_le_contravar: real.

Lemma Ropp_ge_contravar : forall r1 r2, r2 >= r1 -> - r1 >= - r2.
Proof. auto using Ropp_le_contravar with real. Qed.

(**********)
Lemma Ropp_0_lt_gt_contravar : forall r, 0 < r -> 0 > - r.
Proof.
  intros; replace 0 with (-0); auto with real.
Qed.
Hint Resolve Ropp_0_lt_gt_contravar: real.

Lemma Ropp_0_gt_lt_contravar : forall r, 0 > r -> 0 < - r.
Proof.
  intros; replace 0 with (-0); auto with real.
Qed.
Hint Resolve Ropp_0_gt_lt_contravar: real.

(**********)
Lemma Ropp_lt_gt_0_contravar : forall r, r > 0 -> - r < 0.
Proof.
  intros; rewrite <- Ropp_0; auto with real.
Qed.
Hint Resolve Ropp_lt_gt_0_contravar: real.

Lemma Ropp_gt_lt_0_contravar : forall r, r < 0 -> - r > 0.
Proof.
  intros; rewrite <- Ropp_0; auto with real.
Qed.
Hint Resolve Ropp_gt_lt_0_contravar: real.

(**********)
Lemma Ropp_0_le_ge_contravar : forall r, 0 <= r -> 0 >= - r.
Proof.
  intros; replace 0 with (-0); auto with real.
Qed.
Hint Resolve Ropp_0_le_ge_contravar: real.

Lemma Ropp_0_ge_le_contravar : forall r, 0 >= r -> 0 <= - r.
Proof.
  intros; replace 0 with (-0); auto with real.
Qed.
Hint Resolve Ropp_0_ge_le_contravar: real.

(** *** Cancellation *)

Lemma Ropp_lt_cancel : forall r1 r2, - r2 < - r1 -> r1 < r2.
Proof.
  intros x y H'.
  rewrite <- (Ropp_involutive x); rewrite <- (Ropp_involutive y);
    auto with real.
Qed.
Hint Immediate Ropp_lt_cancel: real.

Lemma Ropp_gt_cancel : forall r1 r2, - r2 > - r1 -> r1 > r2.
Proof. auto using Ropp_lt_cancel with rorders. Qed.

Lemma Ropp_le_cancel : forall r1 r2, - r2 <= - r1 -> r1 <= r2.
Proof.
  intros x y H.
  elim H; auto with real.
  intro H1; rewrite <- (Ropp_involutive x); rewrite <- (Ropp_involutive y);
    rewrite H1; auto with real.
Qed.
Hint Immediate Ropp_le_cancel: real.

Lemma Ropp_ge_cancel : forall r1 r2, - r2 >= - r1 -> r1 >= r2.
Proof. auto using Ropp_le_cancel with rorders. Qed.

(*********************************************************)
(** ** Order and multiplication                          *)
(*********************************************************)

(** Remark: [Rmult_lt_compat_l] is an axiom *)

(** *** Covariant compatibility *)

Lemma Rmult_lt_compat_r : forall r r1 r2, 0 < r -> r1 < r2 -> r1 * r < r2 * r.
Proof.
  intros; rewrite (Rmult_comm r1 r); rewrite (Rmult_comm r2 r); auto with real.
Qed.
Hint Resolve Rmult_lt_compat_r : core.

Lemma Rmult_gt_compat_r : forall r r1 r2, r > 0 -> r1 > r2 -> r1 * r > r2 * r.
Proof. eauto using Rmult_lt_compat_r with rorders. Qed.

Lemma Rmult_gt_compat_l : forall r r1 r2, r > 0 -> r1 > r2 -> r * r1 > r * r2.
Proof. eauto using Rmult_lt_compat_l with rorders. Qed.

(**********)
Lemma Rmult_le_compat_l :
  forall r r1 r2, 0 <= r -> r1 <= r2 -> r * r1 <= r * r2.
Proof.
  intros r r1 r2 H H0; destruct H; destruct H0; unfold Rle;
    auto with real.
  right; rewrite <- H; do 2 rewrite Rmult_0_l; reflexivity.
Qed.
Hint Resolve Rmult_le_compat_l: real.

Lemma Rmult_le_compat_r :
  forall r r1 r2, 0 <= r -> r1 <= r2 -> r1 * r <= r2 * r.
Proof.
  intros r r1 r2 H; rewrite (Rmult_comm r1 r); rewrite (Rmult_comm r2 r);
    auto with real.
Qed.
Hint Resolve Rmult_le_compat_r: real.

Lemma Rmult_ge_compat_l :
  forall r r1 r2, r >= 0 -> r1 >= r2 -> r * r1 >= r * r2.
Proof. eauto using Rmult_le_compat_l with rorders. Qed.

Lemma Rmult_ge_compat_r :
  forall r r1 r2, r >= 0 -> r1 >= r2 -> r1 * r >= r2 * r.
Proof. eauto using Rmult_le_compat_r with rorders. Qed.

(**********)
Lemma Rmult_le_compat :
  forall r1 r2 r3 r4,
    0 <= r1 -> 0 <= r3 -> r1 <= r2 -> r3 <= r4 -> r1 * r3 <= r2 * r4.
Proof.
  intros. rewrite Rrepr_le, Rrepr_mult, Rrepr_mult.
  apply Rmult_le_compat. rewrite <- Rrepr_0, <- Rrepr_le. exact H.
  rewrite <- Rrepr_0, <- Rrepr_le. exact H0.
  rewrite <- Rrepr_le. exact H1. rewrite <- Rrepr_le. exact H2.
Qed.
Hint Resolve Rmult_le_compat: real.

Lemma Rmult_ge_compat :
  forall r1 r2 r3 r4,
    r2 >= 0 -> r4 >= 0 -> r1 >= r2 -> r3 >= r4 -> r1 * r3 >= r2 * r4.
Proof. auto with real rorders. Qed.

Lemma Rmult_gt_0_lt_compat :
  forall r1 r2 r3 r4,
    r3 > 0 -> r2 > 0 -> r1 < r2 -> r3 < r4 -> r1 * r3 < r2 * r4.
Proof.
  intros; apply Rlt_trans with (r2 * r3); auto with real.
Qed.

(*********)
Lemma Rmult_le_0_lt_compat :
  forall r1 r2 r3 r4,
    0 <= r1 -> 0 <= r3 -> r1 < r2 -> r3 < r4 -> r1 * r3 < r2 * r4.
Proof.
  intros; apply Rle_lt_trans with (r2 * r3);
    [ apply Rmult_le_compat_r; [ assumption | left; assumption ]
      | apply Rmult_lt_compat_l;
        [ apply Rle_lt_trans with r1; assumption | assumption ] ].
Qed.

(*********)
Lemma Rmult_lt_0_compat : forall r1 r2, 0 < r1 -> 0 < r2 -> 0 < r1 * r2.
Proof. intros; replace 0 with (0 * r2); auto with real. Qed.

Lemma Rmult_gt_0_compat : forall r1 r2, r1 > 0 -> r2 > 0 -> r1 * r2 > 0.
Proof Rmult_lt_0_compat.

(** *** Contravariant compatibility *)

Lemma Rmult_le_compat_neg_l :
  forall r r1 r2, r <= 0 -> r1 <= r2 -> r * r2 <= r * r1.
Proof.
  intros; replace r with (- - r); auto with real.
  do 2 rewrite (Ropp_mult_distr_l_reverse (- r)).
  apply Ropp_le_contravar; auto with real.
Qed.
Hint Resolve Rmult_le_compat_neg_l: real.

Lemma Rmult_le_ge_compat_neg_l :
  forall r r1 r2, r <= 0 -> r1 <= r2 -> r * r1 >= r * r2.
Proof.
  intros; apply Rle_ge; auto with real.
Qed.
Hint Resolve Rmult_le_ge_compat_neg_l: real.

Lemma Rmult_lt_gt_compat_neg_l :
  forall r r1 r2, r < 0 -> r1 < r2 -> r * r1 > r * r2.
Proof.
  intros; replace r with (- - r); auto with real.
  rewrite (Ropp_mult_distr_l_reverse (- r));
    rewrite (Ropp_mult_distr_l_reverse (- r)).
  apply Ropp_lt_gt_contravar; auto with real.
Qed.

(** *** Cancellation *)

Lemma Rmult_lt_reg_l : forall r r1 r2, 0 < r -> r * r1 < r * r2 -> r1 < r2.
Proof.
  intros. rewrite Rlt_def in H,H0. rewrite Rlt_def.
  apply (Rmult_lt_reg_l (Rrepr r)).
  rewrite <- Rrepr_0. exact H.
  rewrite <- Rrepr_mult, <- Rrepr_mult. exact H0.
Qed.

Lemma Rmult_lt_reg_r : forall r r1 r2 : R, 0 < r -> r1 * r < r2 * r -> r1 < r2.
Proof.
  intros. rewrite Rlt_def. rewrite Rlt_def in H, H0.
  apply (Rmult_lt_reg_r (Rrepr r)).
  rewrite <- Rrepr_0. exact H.
  rewrite <- Rrepr_mult, <- Rrepr_mult. exact H0.
Qed.

Lemma Rmult_gt_reg_l : forall r r1 r2, 0 < r -> r * r1 < r * r2 -> r1 < r2.
Proof. eauto using Rmult_lt_reg_l with rorders. Qed.

Lemma Rmult_le_reg_l : forall r r1 r2, 0 < r -> r * r1 <= r * r2 -> r1 <= r2.
Proof.
  intros. rewrite Rrepr_le. rewrite Rlt_def in H. apply (Rmult_le_reg_l (Rrepr r)).
  rewrite <- Rrepr_0. exact H.
  rewrite <- Rrepr_mult, <- Rrepr_mult.
  rewrite <- Rrepr_le. exact H0.
Qed.

Lemma Rmult_le_reg_r : forall r r1 r2, 0 < r -> r1 * r <= r2 * r -> r1 <= r2.
Proof.
  intros.
  apply Rmult_le_reg_l with r.
  exact H.
  now rewrite 2!(Rmult_comm r).
Qed.

(*********************************************************)
(** ** Order and subtraction                             *)
(*********************************************************)

Lemma Rlt_minus : forall r1 r2, r1 < r2 -> r1 - r2 < 0.
Proof.
  intros; apply (Rplus_lt_reg_l r2).
  replace (r2 + (r1 - r2)) with r1 by ring.
  now rewrite Rplus_0_r.
Qed.
Hint Resolve Rlt_minus: real.

Lemma Rgt_minus : forall r1 r2, r1 > r2 -> r1 - r2 > 0.
Proof.
  intros; apply (Rplus_lt_reg_l r2).
  replace (r2 + (r1 - r2)) with r1 by ring.
  now rewrite Rplus_0_r.
Qed.

Lemma Rlt_Rminus : forall a b:R, a < b -> 0 < b - a.
Proof.
  intros a b; apply Rgt_minus.
Qed.

(**********)
Lemma Rle_minus : forall r1 r2, r1 <= r2 -> r1 - r2 <= 0.
Proof.
  destruct 1; unfold Rle; auto with real.
Qed.

Lemma Rge_minus : forall r1 r2, r1 >= r2 -> r1 - r2 >= 0.
Proof.
  destruct 1.
    auto using Rgt_minus, Rgt_ge.
    right; auto using Rminus_diag_eq with rorders.
Qed.

(**********)
Lemma Rminus_lt : forall r1 r2, r1 - r2 < 0 -> r1 < r2.
Proof.
  intros; replace r1 with (r1 - r2 + r2).
  pattern r2 at 3; replace r2 with (0 + r2); auto with real.
  ring.
Qed.

Lemma Rminus_gt : forall r1 r2, r1 - r2 > 0 -> r1 > r2.
Proof.
  intros; replace r2 with (0 + r2); auto with real.
  replace r1 with (r1 - r2 + r2).
  apply Rplus_gt_compat_r; assumption.
  ring.
Qed.

Lemma Rminus_gt_0_lt : forall a b, 0 < b - a -> a < b.
Proof. intro; intro; apply Rminus_gt. Qed.

(**********)
Lemma Rminus_le : forall r1 r2, r1 - r2 <= 0 -> r1 <= r2.
Proof.
  intros; replace r1 with (r1 - r2 + r2).
  pattern r2 at 3; replace r2 with (0 + r2); auto with real.
  ring.
Qed.

Lemma Rminus_ge : forall r1 r2, r1 - r2 >= 0 -> r1 >= r2.
Proof.
  intros; replace r2 with (0 + r2); auto with real.
  replace r1 with (r1 - r2 + r2).
  apply Rplus_ge_compat_r; assumption.
  ring.
Qed.

(**********)
Lemma tech_Rplus : forall r (s:R), 0 <= r -> 0 < s -> r + s <> 0.
Proof.
  intros; apply not_eq_sym; apply Rlt_not_eq.
  rewrite Rplus_comm; replace 0 with (0 + 0); auto with real.
Qed.
Hint Immediate tech_Rplus: real.

(*********************************************************)
(** ** Order and square function                         *)
(*********************************************************)

Lemma Rle_0_sqr : forall r, 0 <= Rsqr r.
Proof.
  intro; case (Rlt_le_dec r 0); unfold Rsqr; intro.
  replace (r * r) with (- r * - r); auto with real.
  replace 0 with (- r * 0); auto with real.
  replace 0 with (0 * r); auto with real.
Qed.

(***********)
Lemma Rlt_0_sqr : forall r, r <> 0 -> 0 < Rsqr r.
Proof.
  intros; case (Rdichotomy r 0); trivial; unfold Rsqr; intro.
  replace (r * r) with (- r * - r); auto with real.
  replace 0 with (- r * 0); auto with real.
  replace 0 with (0 * r); auto with real.
Qed.
Hint Resolve Rle_0_sqr Rlt_0_sqr: real.

(***********)
Lemma Rplus_sqr_eq_0_l : forall r1 r2, Rsqr r1 + Rsqr r2 = 0 -> r1 = 0.
Proof.
  intros a b; intros; apply Rsqr_0_uniq; apply Rplus_eq_0_l with (Rsqr b);
    auto with real.
Qed.

Lemma Rplus_sqr_eq_0 :
  forall r1 r2, Rsqr r1 + Rsqr r2 = 0 -> r1 = 0 /\ r2 = 0.
Proof.
  intros a b; split.
  apply Rplus_sqr_eq_0_l with b; auto with real.
  apply Rplus_sqr_eq_0_l with a; auto with real.
  rewrite Rplus_comm; auto with real.
Qed.

(*********************************************************)
(** ** Zero is less than one                             *)
(*********************************************************)

Lemma Rlt_0_1 : 0 < 1.
Proof.
  replace 1 with (Rsqr 1); auto with real.
  unfold Rsqr; auto with real.
Qed.
Hint Resolve Rlt_0_1: real.

Lemma Rle_0_1 : 0 <= 1.
Proof.
  left.
  exact Rlt_0_1.
Qed.

(*********************************************************)
(** ** Order and inverse                                 *)
(*********************************************************)

Lemma Rinv_0_lt_compat : forall r, 0 < r -> 0 < / r.
Proof.
  intros; apply Rnot_le_lt; red; intros.
  absurd (1 <= 0); auto with real.
  replace 1 with (r * / r); auto with real.
  replace 0 with (r * 0); auto with real.
Qed.
Hint Resolve Rinv_0_lt_compat: real.

(*********)
Lemma Rinv_lt_0_compat : forall r, r < 0 -> / r < 0.
Proof.
  intros; apply Rnot_le_lt; red; intros.
  absurd (1 <= 0); auto with real.
  replace 1 with (r * / r); auto with real.
  replace 0 with (r * 0); auto with real.
Qed.
Hint Resolve Rinv_lt_0_compat: real.

(*********)
Lemma Rinv_lt_contravar : forall r1 r2, 0 < r1 * r2 -> r1 < r2 -> / r2 < / r1.
Proof.
  intros; apply Rmult_lt_reg_l with (r1 * r2); auto with real.
  case (Rmult_neq_0_reg r1 r2); intros; auto with real.
  replace (r1 * r2 * / r2) with r1.
  replace (r1 * r2 * / r1) with r2; trivial.
  symmetry ; auto with real.
  symmetry ; auto with real.
Qed.

Lemma Rinv_1_lt_contravar : forall r1 r2, 1 <= r1 -> r1 < r2 -> / r2 < / r1.
Proof.
 intros x y H' H'0.
  cut (0 < x); [ intros Lt0 | apply Rlt_le_trans with (r2 := 1) ];
    auto with real.
  apply Rmult_lt_reg_l with (r := x); auto with real.
  rewrite (Rmult_comm x (/ x)); rewrite Rinv_l; auto with real.
  apply Rmult_lt_reg_l with (r := y); auto with real.
  apply Rlt_trans with (r2 := x); auto.
  cut (y * (x * / y) = x).
  intro H1; rewrite H1; rewrite (Rmult_1_r y); auto.
  rewrite (Rmult_comm x); rewrite <- Rmult_assoc; rewrite (Rmult_comm y (/ y));
    rewrite Rinv_l; auto with real.
  apply Rlt_dichotomy_converse; right.
  red; apply Rlt_trans with (r2 := x); auto with real.
Qed.
Hint Resolve Rinv_1_lt_contravar: real.

(*********************************************************)
(** ** Miscellaneous                                     *)
(*********************************************************)

(**********)
Lemma Rle_lt_0_plus_1 : forall r, 0 <= r -> 0 < r + 1.
Proof.
  intros.
  apply Rlt_le_trans with 1; auto with real.
  pattern 1 at 1; replace 1 with (0 + 1); auto with real.
Qed.
Hint Resolve Rle_lt_0_plus_1: real.

(**********)
Lemma Rlt_plus_1 : forall r, r < r + 1.
Proof.
  intros.
  pattern r at 1; replace r with (r + 0); auto with real.
Qed.
Hint Resolve Rlt_plus_1: real.

(**********)
Lemma tech_Rgt_minus : forall r1 r2, 0 < r2 -> r1 > r1 - r2.
Proof.
  red; unfold Rminus; intros.
  pattern r1 at 2; replace r1 with (r1 + 0); auto with real.
Qed.

(*********************************************************)
(** ** Injection from [N] to [R]                         *)
(*********************************************************)

(**********)
Lemma S_INR : forall n:nat, INR (S n) = INR n + 1.
Proof.
  intro; case n; auto with real.
Qed.

(**********)
Lemma S_O_plus_INR : forall n:nat, INR (1 + n) = INR 1 + INR n.
Proof.
  intro; simpl; case n; intros; auto with real.
Qed.

(**********)
Lemma plus_INR : forall n m:nat, INR (n + m) = INR n + INR m.
Proof.
  intros. apply Rquot1.
  rewrite Rrepr_INR, Rrepr_plus, plus_INR,
  <- Rrepr_INR, <- Rrepr_INR. reflexivity.
Qed.
Hint Resolve plus_INR: real.

(**********)
Lemma minus_INR : forall n m:nat, (m <= n)%nat -> INR (n - m) = INR n - INR m.
Proof.
  intros n m le; pattern m, n; apply le_elim_rel; auto with real.
  intros; rewrite <- minus_n_O; auto with real.
  intros; repeat rewrite S_INR; simpl.
  rewrite H0; ring.
Qed.
Hint Resolve minus_INR: real.

(*********)
Lemma mult_INR : forall n m:nat, INR (n * m) = INR n * INR m.
Proof.
  intros n m; induction  n as [| n Hrecn].
  simpl; auto with real.
  intros; repeat rewrite S_INR; simpl.
  rewrite plus_INR; rewrite Hrecn; ring.
Qed.
Hint Resolve mult_INR: real.

Lemma pow_INR (m n: nat) :  INR (m ^ n) = pow (INR m) n.
Proof. now induction n as [|n IHn];[ | simpl; rewrite mult_INR, IHn]. Qed.

(*********)
Lemma lt_0_INR : forall n:nat, (0 < n)%nat -> 0 < INR n.
Proof.
  simple induction 1; intros; auto with real.
  rewrite S_INR; auto with real.
Qed.
Hint Resolve lt_0_INR: real.

Lemma lt_INR : forall n m:nat, (n < m)%nat -> INR n < INR m.
Proof.
  simple induction 1; intros; auto with real.
  rewrite S_INR; auto with real.
  rewrite S_INR; apply Rlt_trans with (INR m0); auto with real.
Qed.
Hint Resolve lt_INR: real.

Lemma lt_1_INR : forall n:nat, (1 < n)%nat -> 1 < INR n.
Proof.
  apply lt_INR.
Qed.
Hint Resolve lt_1_INR: real.

(**********)
Lemma pos_INR_nat_of_P : forall p:positive, 0 < INR (Pos.to_nat p).
Proof.
  intro; apply lt_0_INR.
  simpl; auto with real.
  apply Pos2Nat.is_pos.
Qed.
Hint Resolve pos_INR_nat_of_P: real.

(**********)
Lemma pos_INR : forall n:nat, 0 <= INR n.
Proof.
  intro n; case n.
  simpl; auto with real.
  auto with arith real.
Qed.
Hint Resolve pos_INR: real.

Lemma INR_lt : forall n m:nat, INR n < INR m -> (n < m)%nat.
Proof.
  intros. apply INR_lt. rewrite Rlt_def in H.
  rewrite Rrepr_INR, Rrepr_INR in H. exact H.
Qed.
Hint Resolve INR_lt: real.

(*********)
Lemma le_INR : forall n m:nat, (n <= m)%nat -> INR n <= INR m.
Proof.
  simple induction 1; intros; auto with real.
  rewrite S_INR.
  apply Rle_trans with (INR m0); auto with real.
Qed.
Hint Resolve le_INR: real.

(**********)
Lemma INR_not_0 : forall n:nat, INR n <> 0 -> n <> 0%nat.
Proof.
  red; intros n H H1.
  apply H.
  rewrite H1; trivial.
Qed.
Hint Immediate INR_not_0: real.

(**********)
Lemma not_0_INR : forall n:nat, n <> 0%nat -> INR n <> 0.
Proof.
  intro n; case n.
  intro; absurd (0%nat = 0%nat); trivial.
  intros; rewrite S_INR.
  apply Rgt_not_eq; red; auto with real.
Qed.
Hint Resolve not_0_INR: real.

Lemma not_INR : forall n m:nat, n <> m -> INR n <> INR m.
Proof.
  intros. rewrite Rrepr_appart, Rrepr_INR, Rrepr_INR.
  apply not_INR. exact H.
Qed.
Hint Resolve not_INR: real.

Lemma INR_eq : forall n m:nat, INR n = INR m -> n = m.
Proof.
  intros n m HR.
  destruct (dec_eq_nat n m) as [H|H].
  exact H.
  now apply not_INR in H.
Qed.
Hint Resolve INR_eq: real.

Lemma INR_le : forall n m:nat, INR n <= INR m -> (n <= m)%nat.
Proof.
  intros; elim H; intro.
  generalize (INR_lt n m H0); intro; auto with arith.
  generalize (INR_eq n m H0); intro; rewrite H1; auto.
Qed.
Hint Resolve INR_le: real.

Lemma not_1_INR : forall n:nat, n <> 1%nat -> INR n <> 1.
Proof.
  intros n.
  apply not_INR.
Qed.
Hint Resolve not_1_INR: real.

(*********************************************************)
(** ** Injection from [Z] to [R]                         *)
(*********************************************************)


(**********)
Lemma IZN : forall n:Z, (0 <= n)%Z ->  exists m : nat, n = Z.of_nat m.
Proof.
  intros z; idtac; apply Z_of_nat_complete; assumption.
Qed.

Lemma INR_IPR : forall p, INR (Pos.to_nat p) = IPR p.
Proof.
  intros. apply Rquot1. rewrite Rrepr_INR, Rrepr_IPR.
  apply INR_IPR.
Qed.

(**********)
Lemma INR_IZR_INZ : forall n:nat, INR n = IZR (Z.of_nat n).
Proof.
  intros [|n].
  easy.
  simpl Z.of_nat. unfold IZR.
  now rewrite <- INR_IPR, SuccNat2Pos.id_succ.
Qed.

Lemma plus_IZR_NEG_POS :
  forall p q:positive, IZR (Zpos p + Zneg q) = IZR (Zpos p) + IZR (Zneg q).
Proof.
  intros. apply Rquot1. rewrite Rrepr_plus.
  do 3 rewrite Rrepr_IZR. apply plus_IZR_NEG_POS.
Qed.

(**********)
Lemma plus_IZR : forall n m:Z, IZR (n + m) = IZR n + IZR m.
Proof.
  intros. apply Rquot1.
  rewrite Rrepr_plus. do 3 rewrite Rrepr_IZR. apply plus_IZR.
Qed.

(**********)
Lemma mult_IZR : forall n m:Z, IZR (n * m) = IZR n * IZR m.
Proof.
  intros z t; case z; case t; simpl; auto with real;
    unfold IZR; intros m n; rewrite <- 3!INR_IPR, Pos2Nat.inj_mul, mult_INR; ring.
Qed.

Lemma Rrepr_pow : forall (x : R) (n : nat),
    (ConstructiveCauchyReals.CRealEq (Rrepr (pow x n))
                                     (ConstructiveCauchyReals.pow (Rrepr x) n)).
Proof.
  intro x. induction n.
  - apply Rrepr_1.
  - simpl. rewrite Rrepr_mult, <- IHn. reflexivity.
Qed.

Lemma pow_IZR : forall z n, pow (IZR z) n = IZR (Z.pow z (Z.of_nat n)).
Proof.
  intros. apply Rquot1.
  rewrite Rrepr_IZR, Rrepr_pow.
  rewrite (Rpow_eq_compat _ _ n (Rrepr_IZR z)).
  apply pow_IZR.
Qed.

(**********)
Lemma succ_IZR : forall n:Z, IZR (Z.succ n) = IZR n + 1.
Proof.
  intro; unfold Z.succ; apply plus_IZR.
Qed.

(**********)
Lemma opp_IZR : forall n:Z, IZR (- n) = - IZR n.
Proof.
  intros [|z|z]; unfold IZR; simpl; auto with real.
Qed.

Definition Ropp_Ropp_IZR := opp_IZR.

Lemma minus_IZR : forall n m:Z, IZR (n - m) = IZR n - IZR m.
Proof.
  intros; unfold Z.sub, Rminus.
  rewrite <- opp_IZR.
  apply plus_IZR.
Qed.

(**********)
Lemma Z_R_minus : forall n m:Z, IZR n - IZR m = IZR (n - m).
Proof.
  intros z1 z2; unfold Rminus; unfold Z.sub.
  rewrite <- (Ropp_Ropp_IZR z2); symmetry ; apply plus_IZR.
Qed.

(**********)
Lemma lt_0_IZR : forall n:Z, 0 < IZR n -> (0 < n)%Z.
Proof.
  intros. apply lt_0_IZR. rewrite <- Rrepr_0, <- Rrepr_IZR.
  rewrite Rlt_def in H. exact H.
Qed.

(**********)
Lemma lt_IZR : forall n m:Z, IZR n < IZR m -> (n < m)%Z.
Proof.
  intros. apply lt_IZR.
  rewrite <- Rrepr_IZR, <- Rrepr_IZR. rewrite Rlt_def in H. exact H.
Qed.

(**********)
Lemma eq_IZR_R0 : forall n:Z, IZR n = 0 -> n = 0%Z.
Proof.
  intros. apply eq_IZR_R0.
  rewrite <- Rrepr_0, <- Rrepr_IZR, H. reflexivity.
Qed.

(**********)
Lemma eq_IZR : forall n m:Z, IZR n = IZR m -> n = m.
Proof.
  intros z1 z2 H; generalize (Rminus_diag_eq (IZR z1) (IZR z2) H);
    rewrite (Z_R_minus z1 z2); intro; generalize (eq_IZR_R0 (z1 - z2) H0);
      intro; omega.
Qed.

(**********)
Lemma not_0_IZR : forall n:Z, n <> 0%Z -> IZR n <> 0.
Proof.
  intros z H; red; intros H0; case H.
  apply eq_IZR; auto.
Qed.

(*********)
Lemma le_0_IZR : forall n:Z, 0 <= IZR n -> (0 <= n)%Z.
Proof.
  unfold Rle; intros z [H| H].
  red; intro; apply (Z.lt_le_incl 0 z (lt_0_IZR z H)); assumption.
  rewrite (eq_IZR_R0 z); auto with zarith real.
Qed.

(**********)
Lemma le_IZR : forall n m:Z, IZR n <= IZR m -> (n <= m)%Z.
Proof.
  unfold Rle; intros z1 z2 [H| H].
  apply (Z.lt_le_incl z1 z2); auto with real.
  apply lt_IZR; trivial.
  rewrite (eq_IZR z1 z2); auto with zarith real.
Qed.

(**********)
Lemma le_IZR_R1 : forall n:Z, IZR n <= 1 -> (n <= 1)%Z.
Proof.
  intros n.
  apply le_IZR.
Qed.

(**********)
Lemma IZR_ge : forall n m:Z, (n >= m)%Z -> IZR n >= IZR m.
Proof.
  intros m n H; apply Rnot_lt_ge; red; intro.
  generalize (lt_IZR m n H0); intro; omega.
Qed.

Lemma IZR_le : forall n m:Z, (n <= m)%Z -> IZR n <= IZR m.
Proof.
  intros m n H; apply Rnot_gt_le; red; intro.
  unfold Rgt in H0; generalize (lt_IZR n m H0); intro; omega.
Qed.

Lemma IZR_lt : forall n m:Z, (n < m)%Z -> IZR n < IZR m.
Proof.
  intros m n H; cut (m <= n)%Z.
  intro H0; elim (IZR_le m n H0); intro; auto.
  generalize (eq_IZR m n H1); intro; exfalso; omega.
  omega.
Qed.

Lemma IZR_neq : forall z1 z2:Z, z1 <> z2 -> IZR z1 <> IZR z2.
Proof.
intros; red; intro; elim H; apply eq_IZR; assumption.
Qed.

Hint Extern 0 (IZR _ <= IZR _) => apply IZR_le, Zle_bool_imp_le, eq_refl : real.
Hint Extern 0 (IZR _ >= IZR _) => apply Rle_ge, IZR_le, Zle_bool_imp_le, eq_refl : real.
Hint Extern 0 (IZR _ <  IZR _) => apply IZR_lt, eq_refl : real.
Hint Extern 0 (IZR _ >  IZR _) => apply IZR_lt, eq_refl : real.
Hint Extern 0 (IZR _ <> IZR _) => apply IZR_neq, Zeq_bool_neq, eq_refl : real.

Lemma one_IZR_lt1 : forall n:Z, -1 < IZR n < 1 -> n = 0%Z.
Proof.
  intros. apply one_IZR_lt1. do 2 rewrite Rlt_def in H. split.
  rewrite <- Rrepr_IZR, <- Rrepr_1, <- Rrepr_opp. apply H.
  rewrite <- Rrepr_IZR, <- Rrepr_1. apply H.
Qed.

Lemma one_IZR_r_R1 :
  forall r (n m:Z), r < IZR n <= r + 1 -> r < IZR m <= r + 1 -> n = m.
Proof.
  intros. rewrite Rlt_def in H, H0. apply (one_IZR_r_R1 (Rrepr r)); split.
  rewrite <- Rrepr_IZR. apply H.
  rewrite <- Rrepr_IZR, <- Rrepr_1, <- Rrepr_plus, <- Rrepr_le.
  apply H. rewrite <- Rrepr_IZR. apply H0.
  rewrite <- Rrepr_IZR, <- Rrepr_1, <- Rrepr_plus, <- Rrepr_le.
  apply H0.
Qed.


(**********)
Lemma single_z_r_R1 :
  forall r (n m:Z),
    r < IZR n -> IZR n <= r + 1 -> r < IZR m -> IZR m <= r + 1 -> n = m.
Proof.
  intros; apply one_IZR_r_R1 with r; auto.
Qed.

(**********)
Lemma tech_single_z_r_R1 :
  forall r (n:Z),
    r < IZR n ->
    IZR n <= r + 1 ->
    (exists s : Z, s <> n /\ r < IZR s /\ IZR s <= r + 1) -> False.
Proof.
  intros r z H1 H2 [s [H3 [H4 H5]]].
  apply H3; apply single_z_r_R1 with r; trivial.
Qed.

(*********)
Lemma Rmult_le_pos : forall r1 r2, 0 <= r1 -> 0 <= r2 -> 0 <= r1 * r2.
Proof.
  intros x y H H0; rewrite <- (Rmult_0_l x); rewrite <- (Rmult_comm x);
    apply (Rmult_le_compat_l x 0 y H H0).
Qed.

Lemma Rinv_le_contravar :
  forall x y, 0 < x -> x <= y -> / y <= / x.
Proof.
  intros. apply Rrepr_le. assert (y <> 0).
  intro abs. subst y. apply (Rlt_irrefl 0). exact (Rlt_le_trans 0 x 0 H H0).
  rewrite Rrepr_appart, Rrepr_0 in H1. rewrite Rlt_def in H. rewrite Rrepr_0 in H.
  rewrite (Rrepr_inv y H1), (Rrepr_inv x (or_intror H)).
  apply Rinv_le_contravar. rewrite <- Rrepr_le. exact H0.
Qed.

Lemma Rle_Rinv : forall x y:R, 0 < x -> 0 < y -> x <= y -> / y <= / x.
Proof.
  intros x y H _.
  apply Rinv_le_contravar with (1 := H).
Qed.

Lemma Ropp_div : forall x y, -x/y = - (x / y).
intros x y; unfold Rdiv; ring.
Qed.

Lemma double : forall r1, 2 * r1 = r1 + r1.
Proof.
  intro; ring.
Qed.

Lemma double_var : forall r1, r1 = r1 / 2 + r1 / 2.
Proof.
  intro; rewrite <- double; unfold Rdiv; rewrite <- Rmult_assoc;
    symmetry ; apply Rinv_r_simpl_m.
  now apply not_0_IZR.
Qed.

Lemma R_rm : ring_morph
  0%R 1%R Rplus Rmult Rminus Ropp eq
  0%Z 1%Z Zplus Zmult Zminus Z.opp Zeq_bool IZR.
Proof.
constructor ; try easy.
exact plus_IZR.
exact minus_IZR.
exact mult_IZR.
exact opp_IZR.
intros x y H.
apply f_equal.
now apply Zeq_bool_eq.
Qed.

Lemma Zeq_bool_IZR x y :
  IZR x = IZR y -> Zeq_bool x y = true.
Proof.
intros H.
apply Zeq_is_eq_bool.
now apply eq_IZR.
Qed.

Add Field RField : Rfield
  (completeness Zeq_bool_IZR, morphism R_rm, constants [IZR_tac], power_tac R_power_theory [Rpow_tac]).

(*********************************************************)
(** ** Other rules about < and <=                        *)
(*********************************************************)

Lemma Rmult_ge_0_gt_0_lt_compat :
  forall r1 r2 r3 r4,
    r3 >= 0 -> r2 > 0 -> r1 < r2 -> r3 < r4 -> r1 * r3 < r2 * r4.
Proof.
  intros; apply Rle_lt_trans with (r2 * r3); auto with real.
Qed.

Lemma le_epsilon :
  forall r1 r2, (forall eps:R, 0 < eps -> r1 <= r2 + eps) -> r1 <= r2.
Proof.
  intros. rewrite Rrepr_le. apply le_epsilon.
  intros. rewrite <- (Rquot2 eps), <- Rrepr_plus.
  rewrite <- Rrepr_le. apply H. rewrite Rlt_def.
  rewrite Rquot2, Rrepr_0. exact H0.
Qed.

(**********)
Lemma completeness_weak :
  forall E:R -> Prop,
    bound E -> (exists x : R, E x) ->  exists m : R, is_lub E m.
Proof.
  intros; elim (completeness E H H0); intros; split with x; assumption.
Qed.

Lemma Rdiv_lt_0_compat : forall a b, 0 < a -> 0 < b -> 0 < a/b.
Proof.
intros; apply Rmult_lt_0_compat;[|apply Rinv_0_lt_compat]; assumption.
Qed.

Lemma Rdiv_plus_distr : forall a b c, (a + b)/c = a/c + b/c.
intros a b c; apply Rmult_plus_distr_r.
Qed.

Lemma Rdiv_minus_distr : forall a b c, (a - b)/c = a/c - b/c.
intros a b c; unfold Rminus, Rdiv; rewrite Rmult_plus_distr_r; ring.
Qed.

(* A test for equality function. *)
Lemma Req_EM_T : forall r1 r2:R, {r1 = r2} + {r1 <> r2}.
Proof.
  intros; destruct (total_order_T r1 r2) as [[H|]|H].
  - right; red; intros ->; elim (Rlt_irrefl r2 H).
  - left; assumption.
  - right; red; intros ->; elim (Rlt_irrefl r2 H).
Qed.


(*********************************************************)
(** * Definitions of new types                           *)
(*********************************************************)

Record nonnegreal : Type := mknonnegreal
  {nonneg :> R; cond_nonneg : 0 <= nonneg}.

Record posreal : Type := mkposreal {pos :> R; cond_pos : 0 < pos}.

Record nonposreal : Type := mknonposreal
  {nonpos :> R; cond_nonpos : nonpos <= 0}.

Record negreal : Type := mknegreal {neg :> R; cond_neg : neg < 0}.

Record nonzeroreal : Type := mknonzeroreal
  {nonzero :> R; cond_nonzero : nonzero <> 0}.


(** Compatibility *)

Notation prod_neq_R0 := Rmult_integral_contrapositive_currified (only parsing).
Notation minus_Rgt := Rminus_gt (only parsing).
Notation minus_Rge := Rminus_ge (only parsing).
Notation plus_le_is_le := Rplus_le_reg_pos_r (only parsing).
Notation plus_lt_is_lt := Rplus_lt_reg_pos_r (only parsing).
Notation INR_lt_1 := lt_1_INR (only parsing).
Notation lt_INR_0 := lt_0_INR (only parsing).
Notation not_nm_INR := not_INR (only parsing).
Notation INR_pos := pos_INR_nat_of_P (only parsing).
Notation not_INR_O := INR_not_0 (only parsing).
Notation not_O_INR := not_0_INR (only parsing).
Notation not_O_IZR := not_0_IZR (only parsing).
Notation le_O_IZR := le_0_IZR (only parsing).
Notation lt_O_IZR := lt_0_IZR (only parsing).
