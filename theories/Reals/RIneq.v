(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(***************************************************************************)
(**              Basic lemmas for the classical reals numbers              *)
(***************************************************************************)

Require Export Raxioms.
Require Import Rpow_def.
Require Import Zpower.
Require Export ZArithRing.
Require Import Omega.
Require Export RealField.

Open Local Scope Z_scope.
Open Local Scope R_scope.

Implicit Type r : R.

(**************************************************************************)
(** * Relation between orders and equality                                *)
(**************************************************************************)

(**********)
Lemma Rlt_irrefl : forall r, ~ r < r.
Proof.
  generalize Rlt_asym. intuition eauto.
Qed.
Hint Resolve Rlt_irrefl: real.

Lemma Rle_refl : forall r, r <= r.
Proof.
  intro; right; reflexivity.
Qed.

Lemma Rlt_not_eq : forall r1 r2, r1 < r2 -> r1 <> r2.
Proof.
  red in |- *; intros r1 r2 H H0; apply (Rlt_irrefl r1).
  pattern r1 at 2 in |- *; rewrite H0; trivial.
Qed.

Lemma Rgt_not_eq : forall r1 r2, r1 > r2 -> r1 <> r2.
Proof.
  intros; apply sym_not_eq; apply Rlt_not_eq; auto with real.
Qed.

(**********)
Lemma Rlt_dichotomy_converse : forall r1 r2, r1 < r2 \/ r1 > r2 -> r1 <> r2.
Proof.
  generalize Rlt_not_eq Rgt_not_eq. intuition eauto.
Qed.
Hint Resolve Rlt_dichotomy_converse: real.

(** Reasoning by case on equalities and order *)

(**********)
Lemma Req_dec : forall r1 r2, r1 = r2 \/ r1 <> r2.
Proof.
  intros; generalize (total_order_T r1 r2) Rlt_dichotomy_converse;
    intuition eauto 3. 
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


(*********************************************************************************)
(** *     Order Lemma  : relating [<], [>], [<=] and [>=]  	                 *)
(*********************************************************************************)

(**********)
Lemma Rlt_le : forall r1 r2, r1 < r2 -> r1 <= r2.
Proof.
  intros; red in |- *; tauto.
Qed.
Hint Resolve Rlt_le: real.

(**********)
Lemma Rle_ge : forall r1 r2, r1 <= r2 -> r2 >= r1.
Proof.
  destruct 1; red in |- *; auto with real.
Qed.

Hint Immediate Rle_ge: real.

(**********)
Lemma Rge_le : forall r1 r2, r1 >= r2 -> r2 <= r1.
Proof.
  destruct 1; red in |- *; auto with real.
Qed.

Hint Resolve Rge_le: real.

(**********)
Lemma Rnot_le_lt : forall r1 r2, ~ r1 <= r2 -> r2 < r1.
Proof.
  intros r1 r2; generalize (Rtotal_order r1 r2); unfold Rle in |- *; tauto.
Qed.

Hint Immediate Rnot_le_lt: real.

Lemma Rnot_ge_lt : forall r1 r2, ~ r1 >= r2 -> r1 < r2.
Proof.
  intros; apply Rnot_le_lt; auto with real.
Qed.

(**********)
Lemma Rlt_not_le : forall r1 r2, r2 < r1 -> ~ r1 <= r2.
Proof.
  generalize Rlt_asym Rlt_dichotomy_converse; unfold Rle in |- *.
  intuition eauto 3.
Qed.

Lemma Rgt_not_le : forall r1 r2, r1 > r2 -> ~ r1 <= r2.
Proof Rlt_not_le.

Hint Immediate Rlt_not_le: real.

Lemma Rle_not_lt : forall r1 r2, r2 <= r1 -> ~ r1 < r2.
Proof.
  intros r1 r2. generalize (Rlt_asym r1 r2) (Rlt_dichotomy_converse r1 r2).
  unfold Rle in |- *; intuition.
Qed.

(**********)
Lemma Rlt_not_ge : forall r1 r2, r1 < r2 -> ~ r1 >= r2.
Proof.
  generalize Rlt_not_le. unfold Rle, Rge in |- *. intuition eauto 3.
Qed.

Hint Immediate Rlt_not_ge: real.

(**********)
Lemma Req_le : forall r1 r2, r1 = r2 -> r1 <= r2.
Proof.
  unfold Rle in |- *; tauto.
Qed.
Hint Immediate Req_le: real.

Lemma Req_ge : forall r1 r2, r1 = r2 -> r1 >= r2.
Proof.
  unfold Rge in |- *; tauto.
Qed.
Hint Immediate Req_ge: real.

Lemma Req_le_sym : forall r1 r2, r2 = r1 -> r1 <= r2.
Proof.
  unfold Rle in |- *; auto.
Qed.
Hint Immediate Req_le_sym: real.

Lemma Req_ge_sym : forall r1 r2, r2 = r1 -> r1 >= r2.
Proof.
  unfold Rge in |- *; auto.
Qed.
Hint Immediate Req_ge_sym: real.

Lemma Rle_antisym : forall r1 r2, r1 <= r2 -> r2 <= r1 -> r1 = r2.
Proof.
  intros r1 r2; generalize (Rlt_asym r1 r2); unfold Rle in |- *; intuition.
Qed.
Hint Resolve Rle_antisym: real.

(**********)
Lemma Rle_le_eq : forall r1 r2, r1 <= r2 /\ r2 <= r1 <-> r1 = r2.
Proof.
  intuition.
Qed.

Lemma Rlt_eq_compat :
  forall r1 r2 r3 r4, r1 = r2 -> r2 < r4 -> r4 = r3 -> r1 < r3.
Proof.
  intros x x' y y'; intros; replace x with x'; replace y with y'; assumption.
Qed.

(**********)
Lemma Rle_trans : forall r1 r2 r3, r1 <= r2 -> r2 <= r3 -> r1 <= r3.
Proof.
  generalize trans_eq Rlt_trans Rlt_eq_compat.
  unfold Rle in |- *.
  intuition eauto 2.
Qed.

(**********)
Lemma Rle_lt_trans : forall r1 r2 r3, r1 <= r2 -> r2 < r3 -> r1 < r3.
Proof.
  generalize Rlt_trans Rlt_eq_compat. 
  unfold Rle in |- *.
  intuition eauto 2.
Qed.

(**********)
Lemma Rlt_le_trans : forall r1 r2 r3, r1 < r2 -> r2 <= r3 -> r1 < r3.
Proof.
  generalize Rlt_trans Rlt_eq_compat; unfold Rle in |- *; intuition eauto 2.
Qed.


(** Decidability of the order *)
Lemma Rlt_dec : forall r1 r2, {r1 < r2} + {~ r1 < r2}.
Proof.
  intros; generalize (total_order_T r1 r2) (Rlt_dichotomy_converse r1 r2);
    intuition.
Qed.

(**********)
Lemma Rle_dec : forall r1 r2, {r1 <= r2} + {~ r1 <= r2}.
Proof.
  intros r1 r2.
  generalize (total_order_T r1 r2) (Rlt_dichotomy_converse r1 r2).
  intuition eauto 4 with real.
Qed.

(**********)
Lemma Rgt_dec : forall r1 r2, {r1 > r2} + {~ r1 > r2}.
Proof.
  intros; unfold Rgt in |- *; intros; apply Rlt_dec.
Qed.

(**********)
Lemma Rge_dec : forall r1 r2, {r1 >= r2} + {~ r1 >= r2}.
Proof.
  intros; generalize (Rle_dec r2 r1); intuition.
Qed.

Lemma Rlt_le_dec : forall r1 r2, {r1 < r2} + {r2 <= r1}.
Proof.
  intros; generalize (total_order_T r1 r2); intuition.
Qed.

Lemma Rle_or_lt : forall r1 r2, r1 <= r2 \/ r2 < r1.
Proof.
  intros n m; elim (Rlt_le_dec m n); auto with real.
Qed.

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

(****************************************************************)
(** *      Field Lemmas                                         *)
(* This part contains lemma involving the Fields operations     *)
(****************************************************************)
(*********************************************************)
(** **   Addition                                        *)
(*********************************************************)

Lemma Rplus_ne : forall r, r + 0 = r /\ 0 + r = r.
Proof.
  split; ring.
Qed.
Hint Resolve Rplus_ne: real v62.

Lemma Rplus_0_r : forall r, r + 0 = r.
Proof.
  intro; ring.
Qed.
Hint Resolve Rplus_0_r: real.

(**********)
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

(*i New i*)
Hint Resolve (f_equal (A:=R)): real.

Lemma Rplus_eq_compat_l : forall r r1 r2, r1 = r2 -> r + r1 = r + r2.
Proof.
  auto with real.
Qed.

(*i Old i*)Hint Resolve Rplus_eq_compat_l: v62.

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

(**********)
Lemma Rplus_0_r_uniq : forall r r1, r + r1 = r -> r1 = 0.
Proof.
  intros r b; pattern r at 2 in |- *; replace r with (r + 0); eauto with real.
Qed.

(***********************************************************)       
(** **    Multiplication                                   *)
(***********************************************************)

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

Lemma Rinv_r_sym : forall r, r <> 0 -> 1 = r * / r.
Proof.
  intros; field; trivial.
Qed.
Hint Resolve Rinv_l_sym Rinv_r_sym: real.


(**********)
Lemma Rmult_0_r : forall r, r * 0 = 0.
Proof.
  intro; ring.
Qed.
Hint Resolve Rmult_0_r: real v62.

(**********)
Lemma Rmult_0_l : forall r, 0 * r = 0.
Proof.
  intro; ring.
Qed.
Hint Resolve Rmult_0_l: real v62.

(**********)
Lemma Rmult_ne : forall r, r * 1 = r /\ 1 * r = r.
Proof.
  intro; split; ring.
Qed.
Hint Resolve Rmult_ne: real v62.

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

(*i OLD i*)Hint Resolve Rmult_eq_compat_l: v62.

(**********)
Lemma Rmult_eq_reg_l : forall r r1 r2, r * r1 = r * r2 -> r <> 0 -> r1 = r2.
Proof.
  intros; transitivity (/ r * r * r1).
  field; trivial.
  transitivity (/ r * r * r2).
  repeat rewrite Rmult_assoc; rewrite H; trivial.
  field; trivial.
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
  intros r1 r2 H; split; red in |- *; intro; apply H; auto with real.
Qed.

(**********) 
Lemma Rmult_integral_contrapositive :
  forall r1 r2, r1 <> 0 /\ r2 <> 0 -> r1 * r2 <> 0.
Proof.
  red in |- *; intros r1 r2 [H1 H2] H.
  case (Rmult_integral r1 r2); auto with real.
Qed.
Hint Resolve Rmult_integral_contrapositive: real.

(**********) 
Lemma Rmult_plus_distr_r :
  forall r1 r2 r3, (r1 + r2) * r3 = r1 * r3 + r2 * r3.
Proof.
  intros; ring.
Qed.

(** ** Square function *)

(***********)
Definition Rsqr r : R := r * r.

(***********)
Lemma Rsqr_0 : Rsqr 0 = 0.
  unfold Rsqr in |- *; auto with real.
Qed.

(***********)
Lemma Rsqr_0_uniq : forall r, Rsqr r = 0 -> r = 0.
  unfold Rsqr in |- *; intros; elim (Rmult_integral r r H); trivial.
Qed.

(*********************************************************)
(** **   Opposite                                        *)
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
Hint Resolve Ropp_0: real v62.

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
  red in |- *; intros r H H0.
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


(** ** Opposite and multiplication *)

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

Lemma Ropp_mult_distr_r_reverse : forall r1 r2, r1 * - r2 = - (r1 * r2).
Proof.
  intros; ring.
Qed.

(** ** Substraction *)

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
Hint Resolve Ropp_minus_distr': real. 

(**********)
Lemma Rminus_diag_eq : forall r1 r2, r1 = r2 -> r1 - r2 = 0.
Proof.
  intros; rewrite H; ring.
Qed.
Hint Resolve Rminus_diag_eq: real.

(**********)
Lemma Rminus_diag_uniq : forall r1 r2, r1 - r2 = 0 -> r1 = r2.
Proof.
  intros r1 r2; unfold Rminus in |- *; rewrite Rplus_comm; intro.
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
  red in |- *; intros r1 r2 H H0.
  apply H; auto with real.
Qed.
Hint Resolve Rminus_eq_contra: real.

Lemma Rminus_not_eq : forall r1 r2, r1 - r2 <> 0 -> r1 <> r2.
Proof.
  red in |- *; intros; elim H; apply Rminus_diag_eq; auto.
Qed.
Hint Resolve Rminus_not_eq: real.

Lemma Rminus_not_eq_right : forall r1 r2, r2 - r1 <> 0 -> r1 <> r2.
Proof.
  red in |- *; intros; elim H; rewrite H0; ring.
Qed.
Hint Resolve Rminus_not_eq_right: real. 


(**********)
Lemma Rmult_minus_distr_l :
  forall r1 r2 r3, r1 * (r2 - r3) = r1 * r2 - r1 * r3.
Proof.
  intros; ring.
Qed.

(** ** Inverse *)
Lemma Rinv_1 : / 1 = 1.
Proof.
  field.
Qed.
Hint Resolve Rinv_1: real.

(*********)
Lemma Rinv_neq_0_compat : forall r, r <> 0 -> / r <> 0.
Proof.
  red in |- *; intros; apply R1_neq_R0.
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

(** * Field operations and order *)

(** ** Order and addition *)

Lemma Rplus_lt_compat_r : forall r r1 r2, r1 < r2 -> r1 + r < r2 + r.
Proof.
  intros.
  rewrite (Rplus_comm r1 r); rewrite (Rplus_comm r2 r); auto with real.
Qed.

Hint Resolve Rplus_lt_compat_r: real.

(**********)
Lemma Rplus_lt_reg_r : forall r r1 r2, r + r1 < r + r2 -> r1 < r2.
Proof.
  intros; cut (- r + r + r1 < - r + r + r2).
  rewrite Rplus_opp_l.
  elim (Rplus_ne r1); elim (Rplus_ne r2); intros; rewrite <- H3; rewrite <- H1;
    auto with zarith real.
  rewrite Rplus_assoc; rewrite Rplus_assoc;
    apply (Rplus_lt_compat_l (- r) (r + r1) (r + r2) H).
Qed.

(**********)
Lemma Rplus_le_compat_l : forall r r1 r2, r1 <= r2 -> r + r1 <= r + r2.
Proof.
  unfold Rle in |- *; intros; elim H; intro.
  left; apply (Rplus_lt_compat_l r r1 r2 H0).
  right; rewrite <- H0; auto with zarith real.
Qed.

(**********)
Lemma Rplus_le_compat_r : forall r r1 r2, r1 <= r2 -> r1 + r <= r2 + r.
Proof.
  unfold Rle in |- *; intros; elim H; intro.
  left; apply (Rplus_lt_compat_r r r1 r2 H0).
  right; rewrite <- H0; auto with real.
Qed.

Hint Resolve Rplus_le_compat_l Rplus_le_compat_r: real.

(**********)
Lemma Rplus_le_reg_l : forall r r1 r2, r + r1 <= r + r2 -> r1 <= r2.
Proof.
  unfold Rle in |- *; intros; elim H; intro.
  left; apply (Rplus_lt_reg_r r r1 r2 H0).
  right; apply (Rplus_eq_reg_l r r1 r2 H0).
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

(*********)
Lemma Rplus_lt_compat :
  forall r1 r2 r3 r4, r1 < r2 -> r3 < r4 -> r1 + r3 < r2 + r4.
Proof.
  intros; apply Rlt_trans with (r2 + r3); auto with real.
Qed.

Lemma Rplus_le_compat :
  forall r1 r2 r3 r4, r1 <= r2 -> r3 <= r4 -> r1 + r3 <= r2 + r4.
Proof.
  intros; apply Rle_trans with (r2 + r3); auto with real.
Qed.

(*********)
Lemma Rplus_lt_le_compat :
  forall r1 r2 r3 r4, r1 < r2 -> r3 <= r4 -> r1 + r3 < r2 + r4.
Proof.
  intros; apply Rlt_le_trans with (r2 + r3); auto with real.
Qed.

(*********)
Lemma Rplus_le_lt_compat :
  forall r1 r2 r3 r4, r1 <= r2 -> r3 < r4 -> r1 + r3 < r2 + r4.
Proof.
  intros; apply Rle_lt_trans with (r2 + r3); auto with real.
Qed.

Hint Immediate Rplus_lt_compat Rplus_le_compat Rplus_lt_le_compat
  Rplus_le_lt_compat: real.

(** ** Order and Opposite *)

(**********)
Lemma Ropp_gt_lt_contravar : forall r1 r2, r1 > r2 -> - r1 < - r2.
Proof.
  unfold Rgt in |- *; intros.
  apply (Rplus_lt_reg_r (r2 + r1)).
  replace (r2 + r1 + - r1) with r2.
  replace (r2 + r1 + - r2) with r1.
  trivial.
  ring.
  ring.
Qed.
Hint Resolve Ropp_gt_lt_contravar.

(**********)
Lemma Ropp_lt_gt_contravar : forall r1 r2, r1 < r2 -> - r1 > - r2.
Proof.
  unfold Rgt in |- *; auto with real.
Qed.
Hint Resolve Ropp_lt_gt_contravar: real.

Lemma Ropp_lt_cancel : forall r1 r2, - r2 < - r1 -> r1 < r2.
Proof.
  intros x y H'.
  rewrite <- (Ropp_involutive x); rewrite <- (Ropp_involutive y);
    auto with real.
Qed.
Hint Immediate Ropp_lt_cancel: real.

Lemma Ropp_lt_contravar : forall r1 r2, r2 < r1 -> - r1 < - r2.
Proof.
  auto with real.
Qed.
Hint Resolve Ropp_lt_contravar: real.

(**********)
Lemma Ropp_le_ge_contravar : forall r1 r2, r1 <= r2 -> - r1 >= - r2.
Proof.
  unfold Rge in |- *; intros r1 r2 [H| H]; auto with real.
Qed.
Hint Resolve Ropp_le_ge_contravar: real.

Lemma Ropp_le_cancel : forall r1 r2, - r2 <= - r1 -> r1 <= r2.
Proof.
  intros x y H.
  elim H; auto with real.
  intro H1; rewrite <- (Ropp_involutive x); rewrite <- (Ropp_involutive y);
    rewrite H1; auto with real.
Qed.
Hint Immediate Ropp_le_cancel: real.

Lemma Ropp_le_contravar : forall r1 r2, r2 <= r1 -> - r1 <= - r2.
Proof.
  intros r1 r2 H; elim H; auto with real.
Qed.
Hint Resolve Ropp_le_contravar: real.

(**********)
Lemma Ropp_ge_le_contravar : forall r1 r2, r1 >= r2 -> - r1 <= - r2.
Proof.
  unfold Rge in |- *; intros r1 r2 [H| H]; auto with real.
Qed.
Hint Resolve Ropp_ge_le_contravar: real.

(**********)
Lemma Ropp_0_lt_gt_contravar : forall r, 0 < r -> 0 > - r.
Proof.
  intros; replace 0 with (-0); auto with real.
Qed.
Hint Resolve Ropp_0_lt_gt_contravar: real.

(**********)
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

(**********)
Lemma Ropp_gt_lt_0_contravar : forall r, r < 0 -> - r > 0.
Proof.
  intros; rewrite <- Ropp_0; auto with real.
Qed.
Hint Resolve Ropp_lt_gt_0_contravar Ropp_gt_lt_0_contravar: real.

(**********)
Lemma Ropp_0_le_ge_contravar : forall r, 0 <= r -> 0 >= - r.
Proof.
  intros; replace 0 with (-0); auto with real.
Qed.
Hint Resolve Ropp_0_le_ge_contravar: real.

(**********)
Lemma Ropp_0_ge_le_contravar : forall r, 0 >= r -> 0 <= - r.
Proof.
  intros; replace 0 with (-0); auto with real.
Qed.
Hint Resolve Ropp_0_ge_le_contravar: real.

(** ** Order and multiplication *)

Lemma Rmult_lt_compat_r : forall r r1 r2, 0 < r -> r1 < r2 -> r1 * r < r2 * r.
Proof.
  intros; rewrite (Rmult_comm r1 r); rewrite (Rmult_comm r2 r); auto with real.
Qed.
Hint Resolve Rmult_lt_compat_r.

Lemma Rmult_lt_reg_l : forall r r1 r2, 0 < r -> r * r1 < r * r2 -> r1 < r2.
Proof.
  intros z x y H H0.
  case (Rtotal_order x y); intros Eq0; auto; elim Eq0; clear Eq0; intros Eq0.
  rewrite Eq0 in H0; elimtype False; apply (Rlt_irrefl (z * y)); auto.
  generalize (Rmult_lt_compat_l z y x H Eq0); intro; elimtype False;
    generalize (Rlt_trans (z * x) (z * y) (z * x) H0 H1); 
      intro; apply (Rlt_irrefl (z * x)); auto.
Qed.


Lemma Rmult_lt_gt_compat_neg_l :
  forall r r1 r2, r < 0 -> r1 < r2 -> r * r1 > r * r2.
Proof.
  intros; replace r with (- - r); auto with real.
  rewrite (Ropp_mult_distr_l_reverse (- r));
    rewrite (Ropp_mult_distr_l_reverse (- r)).
  apply Ropp_lt_gt_contravar; auto with real.
Qed.

(**********)
Lemma Rmult_le_compat_l :
  forall r r1 r2, 0 <= r -> r1 <= r2 -> r * r1 <= r * r2.
Proof.
  intros r r1 r2 H H0; destruct H; destruct H0; unfold Rle in |- *;
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

Lemma Rmult_le_reg_l : forall r r1 r2, 0 < r -> r * r1 <= r * r2 -> r1 <= r2.
Proof.
  intros z x y H H0; case H0; auto with real.
  intros H1; apply Rlt_le.
  apply Rmult_lt_reg_l with (r := z); auto.
  intros H1; replace x with (/ z * (z * x)); auto with real.
  replace y with (/ z * (z * y)).
  rewrite H1; auto with real.
  rewrite <- Rmult_assoc; rewrite Rinv_l; auto with real.
  rewrite <- Rmult_assoc; rewrite Rinv_l; auto with real.
Qed.

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

Lemma Rmult_le_compat :
  forall r1 r2 r3 r4,
    0 <= r1 -> 0 <= r3 -> r1 <= r2 -> r3 <= r4 -> r1 * r3 <= r2 * r4.
Proof.
  intros x y z t H' H'0 H'1 H'2.
  apply Rle_trans with (r2 := x * t); auto with real.
  repeat rewrite (fun x => Rmult_comm x t).
  apply Rmult_le_compat_l; auto.
  apply Rle_trans with z; auto.
Qed.
Hint Resolve Rmult_le_compat: real.

Lemma Rmult_gt_0_lt_compat :
  forall r1 r2 r3 r4,
    r3 > 0 -> r2 > 0 -> r1 < r2 -> r3 < r4 -> r1 * r3 < r2 * r4.
Proof.
  intros; apply Rlt_trans with (r2 * r3); auto with real.
Qed.

(*********)
Lemma Rmult_ge_0_gt_0_lt_compat :
  forall r1 r2 r3 r4,
    r3 >= 0 -> r2 > 0 -> r1 < r2 -> r3 < r4 -> r1 * r3 < r2 * r4.
Proof.
  intros; apply Rle_lt_trans with (r2 * r3); auto with real.
Qed.


(** ** Order and Substractions *)

Lemma Rlt_minus : forall r1 r2, r1 < r2 -> r1 - r2 < 0.
Proof.
  intros; apply (Rplus_lt_reg_r r2).
  replace (r2 + (r1 - r2)) with r1.
  replace (r2 + 0) with r2; auto with real.
  ring.
Qed.
Hint Resolve Rlt_minus: real.

(**********)
Lemma Rle_minus : forall r1 r2, r1 <= r2 -> r1 - r2 <= 0.
Proof.
  destruct 1; unfold Rle in |- *; auto with real.
Qed.

(**********)
Lemma Rminus_lt : forall r1 r2, r1 - r2 < 0 -> r1 < r2.
Proof.
  intros; replace r1 with (r1 - r2 + r2).
  pattern r2 at 3 in |- *; replace r2 with (0 + r2); auto with real.
  ring.
Qed.

(**********)
Lemma Rminus_le : forall r1 r2, r1 - r2 <= 0 -> r1 <= r2.
Proof.
  intros; replace r1 with (r1 - r2 + r2).
  pattern r2 at 3 in |- *; replace r2 with (0 + r2); auto with real.
  ring.
Qed.

(**********)
Lemma tech_Rplus : forall r (s:R), 0 <= r -> 0 < s -> r + s <> 0.
Proof.
  intros; apply sym_not_eq; apply Rlt_not_eq.
  rewrite Rplus_comm; replace 0 with (0 + 0); auto with real.
Qed.
Hint Immediate tech_Rplus: real.


(** ** Order and the square function *)

Lemma Rle_0_sqr : forall r, 0 <= Rsqr r.
Proof.
  intro; case (Rlt_le_dec r 0); unfold Rsqr in |- *; intro.
  replace (r * r) with (- r * - r); auto with real.
  replace 0 with (- r * 0); auto with real.
  replace 0 with (0 * r); auto with real.
Qed.

(***********)
Lemma Rlt_0_sqr : forall r, r <> 0 -> 0 < Rsqr r.
Proof.
  intros; case (Rdichotomy r 0); trivial; unfold Rsqr in |- *; intro.
  replace (r * r) with (- r * - r); auto with real.
  replace 0 with (- r * 0); auto with real.
  replace 0 with (0 * r); auto with real.
Qed.
Hint Resolve Rle_0_sqr Rlt_0_sqr: real.

(** ** Zero is less than one *)
Lemma Rlt_0_1 : 0 < 1.
Proof.
  replace 1 with (Rsqr 1); auto with real.
  unfold Rsqr in |- *; auto with real.
Qed.
Hint Resolve Rlt_0_1: real.

Lemma Rle_0_1 : 0 <= 1.
Proof.
  left.
  exact Rlt_0_1.
Qed.

(** ** Order and inverse *)
Lemma Rinv_0_lt_compat : forall r, 0 < r -> 0 < / r.
Proof.
  intros; apply Rnot_le_lt; red in |- *; intros.
  absurd (1 <= 0); auto with real.
  replace 1 with (r * / r); auto with real.
  replace 0 with (r * 0); auto with real.
Qed.
Hint Resolve Rinv_0_lt_compat: real.

(*********)
Lemma Rinv_lt_0_compat : forall r, r < 0 -> / r < 0.
Proof.
  intros; apply Rnot_le_lt; red in |- *; intros.
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
  symmetry  in |- *; auto with real.
  symmetry  in |- *; auto with real.
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
  red in |- *; apply Rlt_trans with (r2 := x); auto with real.
Qed.
Hint Resolve Rinv_1_lt_contravar: real.

(********************************************************)        
(** *     Greater                                       *)
(********************************************************)

(**********)
Lemma Rge_antisym : forall r1 r2, r1 >= r2 -> r2 >= r1 -> r1 = r2.
Proof.
  intros; apply Rle_antisym; auto with real.
Qed.

(**********)
Lemma Rnot_lt_ge : forall r1 r2, ~ r1 < r2 -> r1 >= r2.
Proof.
  intros; unfold Rge in |- *; elim (Rtotal_order r1 r2); intro.
  absurd (r1 < r2); trivial.
  case H0; auto.
Qed.

(**********)
Lemma Rnot_lt_le : forall r1 r2, ~ r1 < r2 -> r2 <= r1.
Proof.
  intros; apply Rge_le; apply Rnot_lt_ge; assumption.
Qed.

(**********)
Lemma Rnot_gt_le : forall r1 r2, ~ r1 > r2 -> r1 <= r2.
Proof.
  intros r1 r2 H; apply Rge_le.
  exact (Rnot_lt_ge r2 r1 H).
Qed.

(**********)
Lemma Rgt_ge : forall r1 r2, r1 > r2 -> r1 >= r2.
Proof.
  red in |- *; auto with real.
Qed.


(**********)
Lemma Rge_gt_trans : forall r1 r2 r3, r1 >= r2 -> r2 > r3 -> r1 > r3.
Proof.
  unfold Rgt in |- *; intros; apply Rlt_le_trans with r2; auto with real.
Qed.

(**********)
Lemma Rgt_ge_trans : forall r1 r2 r3, r1 > r2 -> r2 >= r3 -> r1 > r3.
Proof.
  unfold Rgt in |- *; intros; apply Rle_lt_trans with r2; auto with real.
Qed.

(**********)
Lemma Rgt_trans : forall r1 r2 r3, r1 > r2 -> r2 > r3 -> r1 > r3.
Proof.
  unfold Rgt in |- *; intros; apply Rlt_trans with r2; auto with real.
Qed.

(**********)
Lemma Rge_trans : forall r1 r2 r3, r1 >= r2 -> r2 >= r3 -> r1 >= r3.
Proof.
  intros; apply Rle_ge.
  apply Rle_trans with r2; auto with real.
Qed.

(**********)
Lemma Rle_lt_0_plus_1 : forall r, 0 <= r -> 0 < r + 1.
Proof.
  intros.
  apply Rlt_le_trans with 1; auto with real.
  pattern 1 at 1 in |- *; replace 1 with (0 + 1); auto with real.
Qed.
Hint Resolve Rle_lt_0_plus_1: real.

(**********)
Lemma Rlt_plus_1 : forall r, r < r + 1.
Proof.
  intros.
  pattern r at 1 in |- *; replace r with (r + 0); auto with real.
Qed.
Hint Resolve Rlt_plus_1: real.

(**********)
Lemma tech_Rgt_minus : forall r1 r2, 0 < r2 -> r1 > r1 - r2.
Proof.
  red in |- *; unfold Rminus in |- *; intros.
  pattern r1 at 2 in |- *; replace r1 with (r1 + 0); auto with real.
Qed.

(***********)
Lemma Rplus_gt_compat_l : forall r r1 r2, r1 > r2 -> r + r1 > r + r2.
Proof.
  unfold Rgt in |- *; auto with real.
Qed.
Hint Resolve Rplus_gt_compat_l: real.

(***********)
Lemma Rplus_gt_reg_l : forall r r1 r2, r + r1 > r + r2 -> r1 > r2.
Proof.
  unfold Rgt in |- *; intros; apply (Rplus_lt_reg_r r r2 r1 H).
Qed.

(***********)
Lemma Rplus_ge_compat_l : forall r r1 r2, r1 >= r2 -> r + r1 >= r + r2.
Proof.
  intros; apply Rle_ge; auto with real.
Qed.
Hint Resolve Rplus_ge_compat_l: real.

(***********)
Lemma Rplus_ge_reg_l : forall r r1 r2, r + r1 >= r + r2 -> r1 >= r2.
Proof.
  intros; apply Rle_ge; apply Rplus_le_reg_l with r; auto with real.
Qed.

(***********)
Lemma Rmult_ge_compat_r :
  forall r r1 r2, r >= 0 -> r1 >= r2 -> r1 * r >= r2 * r.
Proof.
  intros; apply Rle_ge; apply Rmult_le_compat_r; apply Rge_le; assumption.
Qed.

(***********)
Lemma Rgt_minus : forall r1 r2, r1 > r2 -> r1 - r2 > 0.
Proof.
  intros; replace 0 with (r2 - r2); auto with real.
  unfold Rgt, Rminus in |- *; auto with real.
Qed.

(*********)
Lemma minus_Rgt : forall r1 r2, r1 - r2 > 0 -> r1 > r2.
Proof.
  intros; replace r2 with (r2 + 0); auto with real.
  intros; replace r1 with (r2 + (r1 - r2)); auto with real.
Qed.

(**********)
Lemma Rge_minus : forall r1 r2, r1 >= r2 -> r1 - r2 >= 0.
Proof.
  unfold Rge in |- *; intros; elim H; intro.
  left; apply (Rgt_minus r1 r2 H0).
  right; apply (Rminus_diag_eq r1 r2 H0).
Qed.

(*********)
Lemma minus_Rge : forall r1 r2, r1 - r2 >= 0 -> r1 >= r2.
Proof.
  intros; replace r2 with (r2 + 0); auto with real.
  intros; replace r1 with (r2 + (r1 - r2)); auto with real.
Qed.


(*********)
Lemma Rmult_gt_0_compat : forall r1 r2, r1 > 0 -> r2 > 0 -> r1 * r2 > 0.
Proof.
  unfold Rgt in |- *; intros.
  replace 0 with (0 * r2); auto with real.
Qed.

(*********)
Lemma Rmult_lt_0_compat : forall r1 r2, 0 < r1 -> 0 < r2 -> 0 < r1 * r2.
Proof Rmult_gt_0_compat.

(***********)
Lemma Rplus_eq_0_l :
  forall r1 r2, 0 <= r1 -> 0 <= r2 -> r1 + r2 = 0 -> r1 = 0.
Proof.
  intros a b [H| H] H0 H1; auto with real.
  absurd (0 < a + b).
  rewrite H1; auto with real.
  replace 0 with (0 + 0); auto with real.
Qed.


Lemma Rplus_eq_R0 :
  forall r1 r2, 0 <= r1 -> 0 <= r2 -> r1 + r2 = 0 -> r1 = 0 /\ r2 = 0.
Proof.
  intros a b; split.
  apply Rplus_eq_0_l with b; auto with real.
  apply Rplus_eq_0_l with a; auto with real.
  rewrite Rplus_comm; auto with real.
Qed.


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


(**********************************************************) 
(** *     Injection from [N] to [R]                       *)
(**********************************************************)

(**********)
Lemma S_INR : forall n:nat, INR (S n) = INR n + 1.
Proof.
  intro; case n; auto with real.
Qed.

(**********)
Lemma S_O_plus_INR : forall n:nat, INR (1 + n) = INR 1 + INR n.
Proof.
  intro; simpl in |- *; case n; intros; auto with real.
Qed.

(**********)
Lemma plus_INR : forall n m:nat, INR (n + m) = INR n + INR m. 
Proof.
  intros n m; induction  n as [| n Hrecn].
  simpl in |- *; auto with real.
  replace (S n + m)%nat with (S (n + m)); auto with arith.
  repeat rewrite S_INR.
  rewrite Hrecn; ring.
Qed.

(**********)
Lemma minus_INR : forall n m:nat, (m <= n)%nat -> INR (n - m) = INR n - INR m.
Proof.
  intros n m le; pattern m, n in |- *; apply le_elim_rel; auto with real.
  intros; rewrite <- minus_n_O; auto with real.
  intros; repeat rewrite S_INR; simpl in |- *.
  rewrite H0; ring.
Qed.

(*********)
Lemma mult_INR : forall n m:nat, INR (n * m) = INR n * INR m.
Proof.
  intros n m; induction  n as [| n Hrecn].
  simpl in |- *; auto with real.
  intros; repeat rewrite S_INR; simpl in |- *.
  rewrite plus_INR; rewrite Hrecn; ring.
Qed.

Hint Resolve plus_INR minus_INR mult_INR: real.

(*********)
Lemma lt_INR_0 : forall n:nat, (0 < n)%nat -> 0 < INR n.
Proof.
  simple induction 1; intros; auto with real.
  rewrite S_INR; auto with real.
Qed.
Hint Resolve lt_INR_0: real.

Lemma lt_INR : forall n m:nat, (n < m)%nat -> INR n < INR m.
Proof.
  simple induction 1; intros; auto with real.
  rewrite S_INR; auto with real.
  rewrite S_INR; apply Rlt_trans with (INR m0); auto with real.
Qed.
Hint Resolve lt_INR: real.

Lemma INR_lt_1 : forall n:nat, (1 < n)%nat -> 1 < INR n.
Proof.
  intros; replace 1 with (INR 1); auto with real.
Qed.
Hint Resolve INR_lt_1: real.

(**********)
Lemma INR_pos : forall p:positive, 0 < INR (nat_of_P p).
Proof.
  intro; apply lt_INR_0.
  simpl in |- *; auto with real.
  apply lt_O_nat_of_P.
Qed.
Hint Resolve INR_pos: real.

(**********)
Lemma pos_INR : forall n:nat, 0 <= INR n.
Proof.
  intro n; case n.
  simpl in |- *; auto with real.
  auto with arith real.
Qed.
Hint Resolve pos_INR: real.

Lemma INR_lt : forall n m:nat, INR n < INR m -> (n < m)%nat.
Proof.
  double induction n m; intros.
  simpl in |- *; elimtype False; apply (Rlt_irrefl 0); auto.
  auto with arith.
  generalize (pos_INR (S n0)); intro; cut (INR 0 = 0);
    [ intro H2; rewrite H2 in H0; idtac | simpl in |- *; trivial ]. 
  generalize (Rle_lt_trans 0 (INR (S n0)) 0 H1 H0); intro; elimtype False;
    apply (Rlt_irrefl 0); auto.
  do 2 rewrite S_INR in H1; cut (INR n1 < INR n0).
  intro H2; generalize (H0 n0 H2); intro; auto with arith.
  apply (Rplus_lt_reg_r 1 (INR n1) (INR n0)).
  rewrite Rplus_comm; rewrite (Rplus_comm 1 (INR n0)); trivial.
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
Lemma not_INR_O : forall n:nat, INR n <> 0 -> n <> 0%nat.
Proof.
  red in |- *; intros n H H1.
  apply H.
  rewrite H1; trivial.
Qed.
Hint Immediate not_INR_O: real.

(**********)
Lemma not_O_INR : forall n:nat, n <> 0%nat -> INR n <> 0.
Proof.
  intro n; case n.
  intro; absurd (0%nat = 0%nat); trivial.
  intros; rewrite S_INR.
  apply Rgt_not_eq; red in |- *; auto with real.
Qed.
Hint Resolve not_O_INR: real.

Lemma not_nm_INR : forall n m:nat, n <> m -> INR n <> INR m.
Proof.
  intros n m H; case (le_or_lt n m); intros H1.
  case (le_lt_or_eq _ _ H1); intros H2.
  apply Rlt_dichotomy_converse; auto with real.
  elimtype False; auto.
  apply sym_not_eq; apply Rlt_dichotomy_converse; auto with real.
Qed.
Hint Resolve not_nm_INR: real.

Lemma INR_eq : forall n m:nat, INR n = INR m -> n = m.
Proof.
  intros; case (le_or_lt n m); intros H1.
  case (le_lt_or_eq _ _ H1); intros H2; auto.
  cut (n <> m).
  intro H3; generalize (not_nm_INR n m H3); intro H4; elimtype False; auto.
  omega.
  symmetry  in |- *; cut (m <> n).
  intro H3; generalize (not_nm_INR m n H3); intro H4; elimtype False; auto.
  omega.
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
  replace 1 with (INR 1); auto with real.
Qed.
Hint Resolve not_1_INR: real.

(**********************************************************) 
(** *    Injection from [Z] to [R]                        *)
(**********************************************************)


(**********)
Lemma IZN : forall n:Z, (0 <= n)%Z ->  exists m : nat, n = Z_of_nat m.
Proof.
  intros z; idtac; apply Z_of_nat_complete; assumption.
Qed.

(**********)
Lemma INR_IZR_INZ : forall n:nat, INR n = IZR (Z_of_nat n).
Proof.
  simple induction n; auto with real.
  intros; simpl in |- *; rewrite nat_of_P_o_P_of_succ_nat_eq_succ;
    auto with real.
Qed.

Lemma plus_IZR_NEG_POS :
  forall p q:positive, IZR (Zpos p + Zneg q) = IZR (Zpos p) + IZR (Zneg q).
Proof.
  intros.
  case (lt_eq_lt_dec (nat_of_P p) (nat_of_P q)).
  intros [H| H]; simpl in |- *.
  rewrite nat_of_P_lt_Lt_compare_complement_morphism; simpl in |- *; trivial.
  rewrite (nat_of_P_minus_morphism q p).
  rewrite minus_INR; auto with arith; ring.
  apply ZC2; apply nat_of_P_lt_Lt_compare_complement_morphism; trivial.
  rewrite (nat_of_P_inj p q); trivial.
  rewrite Pcompare_refl; simpl in |- *; auto with real.
  intro H; simpl in |- *.
  rewrite nat_of_P_gt_Gt_compare_complement_morphism; simpl in |- *;
    auto with arith.
  rewrite (nat_of_P_minus_morphism p q).
  rewrite minus_INR; auto with arith; ring.
  apply ZC2; apply nat_of_P_lt_Lt_compare_complement_morphism; trivial.
Qed.

(**********)
Lemma plus_IZR : forall n m:Z, IZR (n + m) = IZR n + IZR m.
Proof.
  intro z; destruct z; intro t; destruct t; intros; auto with real.
  simpl in |- *; intros; rewrite nat_of_P_plus_morphism; auto with real.
  apply plus_IZR_NEG_POS.
  rewrite Zplus_comm; rewrite Rplus_comm; apply plus_IZR_NEG_POS.
  simpl in |- *; intros; rewrite nat_of_P_plus_morphism; rewrite plus_INR;
    auto with real.
Qed.

(**********)
Lemma mult_IZR : forall n m:Z, IZR (n * m) = IZR n * IZR m.
Proof.
  intros z t; case z; case t; simpl in |- *; auto with real.
  intros t1 z1; rewrite nat_of_P_mult_morphism; auto with real.
  intros t1 z1; rewrite nat_of_P_mult_morphism; auto with real.
  rewrite Rmult_comm.
  rewrite Ropp_mult_distr_l_reverse; auto with real.
  apply Ropp_eq_compat; rewrite mult_comm; auto with real.
  intros t1 z1; rewrite nat_of_P_mult_morphism; auto with real.
  rewrite Ropp_mult_distr_l_reverse; auto with real.
  intros t1 z1; rewrite nat_of_P_mult_morphism; auto with real.
  rewrite Rmult_opp_opp; auto with real.
Qed.

Lemma pow_IZR : forall z n, pow (IZR z) n = IZR (Zpower z (Z_of_nat n)).
Proof.
 intros z [|n];simpl;trivial.
 rewrite Zpower_pos_nat.
 rewrite nat_of_P_o_P_of_succ_nat_eq_succ. unfold Zpower_nat;simpl.
 rewrite mult_IZR.
 induction n;simpl;trivial.
 rewrite mult_IZR;ring[IHn].
Qed.

(**********)
Lemma Ropp_Ropp_IZR : forall n:Z, IZR (- n) = - IZR n.
Proof.
  intro z; case z; simpl in |- *; auto with real.
Qed.

(**********)
Lemma Z_R_minus : forall n m:Z, IZR n - IZR m = IZR (n - m).
Proof.
  intros z1 z2; unfold Rminus in |- *; unfold Zminus in |- *.
  rewrite <- (Ropp_Ropp_IZR z2); symmetry  in |- *; apply plus_IZR.
Qed. 

(**********)
Lemma lt_O_IZR : forall n:Z, 0 < IZR n -> (0 < n)%Z.
Proof.
  intro z; case z; simpl in |- *; intros.
  absurd (0 < 0); auto with real.
  unfold Zlt in |- *; simpl in |- *; trivial.
  case Rlt_not_le with (1 := H).
  replace 0 with (-0); auto with real.
Qed.

(**********)
Lemma lt_IZR : forall n m:Z, IZR n < IZR m -> (n < m)%Z.
Proof.
  intros z1 z2 H; apply Zlt_0_minus_lt. 
  apply lt_O_IZR.
  rewrite <- Z_R_minus.
  exact (Rgt_minus (IZR z2) (IZR z1) H).
Qed.

(**********)
Lemma eq_IZR_R0 : forall n:Z, IZR n = 0 -> n = 0%Z.
Proof.
  intro z; destruct z; simpl in |- *; intros; auto with zarith.
  case (Rlt_not_eq 0 (INR (nat_of_P p))); auto with real.
  case (Rlt_not_eq (- INR (nat_of_P p)) 0); auto with real.
  apply Ropp_lt_gt_0_contravar. unfold Rgt in |- *; apply INR_pos.
Qed.

(**********)
Lemma eq_IZR : forall n m:Z, IZR n = IZR m -> n = m.
Proof.
  intros z1 z2 H; generalize (Rminus_diag_eq (IZR z1) (IZR z2) H);
    rewrite (Z_R_minus z1 z2); intro; generalize (eq_IZR_R0 (z1 - z2) H0); 
      intro; omega.
Qed.

(**********)
Lemma not_O_IZR : forall n:Z, n <> 0%Z -> IZR n <> 0.
Proof.
  intros z H; red in |- *; intros H0; case H.
  apply eq_IZR; auto.
Qed.

(*********)
Lemma le_O_IZR : forall n:Z, 0 <= IZR n -> (0 <= n)%Z.
Proof.
  unfold Rle in |- *; intros z [H| H].
  red in |- *; intro; apply (Zlt_le_weak 0 z (lt_O_IZR z H)); assumption.
  rewrite (eq_IZR_R0 z); auto with zarith real.
Qed.

(**********)
Lemma le_IZR : forall n m:Z, IZR n <= IZR m -> (n <= m)%Z.
Proof.
  unfold Rle in |- *; intros z1 z2 [H| H].
  apply (Zlt_le_weak z1 z2); auto with real.
  apply lt_IZR; trivial.
  rewrite (eq_IZR z1 z2); auto with zarith real.
Qed.

(**********)
Lemma le_IZR_R1 : forall n:Z, IZR n <= 1 -> (n <= 1)%Z.
Proof.
  pattern 1 at 1 in |- *; replace 1 with (IZR 1); intros; auto.
  apply le_IZR; trivial.
Qed.

(**********)
Lemma IZR_ge : forall n m:Z, (n >= m)%Z -> IZR n >= IZR m.
Proof.
  intros m n H; apply Rnot_lt_ge; red in |- *; intro.
  generalize (lt_IZR m n H0); intro; omega.
Qed.

Lemma IZR_le : forall n m:Z, (n <= m)%Z -> IZR n <= IZR m.
Proof.
  intros m n H; apply Rnot_gt_le; red in |- *; intro.
  unfold Rgt in H0; generalize (lt_IZR n m H0); intro; omega.
Qed.

Lemma IZR_lt : forall n m:Z, (n < m)%Z -> IZR n < IZR m.
Proof.
  intros m n H; cut (m <= n)%Z.
  intro H0; elim (IZR_le m n H0); intro; auto.
  generalize (eq_IZR m n H1); intro; elimtype False; omega.
  omega.
Qed.

Lemma one_IZR_lt1 : forall n:Z, -1 < IZR n < 1 -> n = 0%Z.
Proof.
  intros z [H1 H2].
  apply Zle_antisym.
  apply Zlt_succ_le; apply lt_IZR; trivial.
  replace 0%Z with (Zsucc (-1)); trivial.
  apply Zlt_le_succ; apply lt_IZR; trivial.
Qed.

Lemma one_IZR_r_R1 :
  forall r (n m:Z), r < IZR n <= r + 1 -> r < IZR m <= r + 1 -> n = m.
Proof.
  intros r z x [H1 H2] [H3 H4].
  cut ((z - x)%Z = 0%Z); auto with zarith.
  apply one_IZR_lt1.
  rewrite <- Z_R_minus; split.
  replace (-1) with (r - (r + 1)).
  unfold Rminus in |- *; apply Rplus_lt_le_compat; auto with real.
  ring.
  replace 1 with (r + 1 - r).
  unfold Rminus in |- *; apply Rplus_le_lt_compat; auto with real.
  ring.
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

(*****************************************************************)
(** * Definitions of new types                                   *)
(*****************************************************************)

Record nonnegreal : Type := mknonnegreal
  {nonneg :> R; cond_nonneg : 0 <= nonneg}.

Record posreal : Type := mkposreal {pos :> R; cond_pos : 0 < pos}.

Record nonposreal : Type := mknonposreal
  {nonpos :> R; cond_nonpos : nonpos <= 0}.

Record negreal : Type := mknegreal {neg :> R; cond_neg : neg < 0}.

Record nonzeroreal : Type := mknonzeroreal
  {nonzero :> R; cond_nonzero : nonzero <> 0}.

(**********)
Lemma prod_neq_R0 : forall r1 r2, r1 <> 0 -> r2 <> 0 -> r1 * r2 <> 0.
Proof.
  intros x y; intros; red in |- *; intro; generalize (Rmult_integral x y H1);
    intro; elim H2; intro;
      [ rewrite H3 in H; elim H | rewrite H3 in H0; elim H0 ]; 
      reflexivity.
Qed.

(*********)
Lemma Rmult_le_pos : forall r1 r2, 0 <= r1 -> 0 <= r2 -> 0 <= r1 * r2.
Proof.
  intros x y H H0; rewrite <- (Rmult_0_l x); rewrite <- (Rmult_comm x);
    apply (Rmult_le_compat_l x 0 y H H0).
Qed.

Lemma double : forall r1, 2 * r1 = r1 + r1.
Proof.
  intro; ring.
Qed.

Lemma double_var : forall r1, r1 = r1 / 2 + r1 / 2.
Proof.
  intro; rewrite <- double; unfold Rdiv in |- *; rewrite <- Rmult_assoc;
    symmetry  in |- *; apply Rinv_r_simpl_m.
  replace 2 with (INR 2);
  [ apply not_O_INR; discriminate | unfold INR in |- *; ring ].
Qed.

(**********************************************************)
(** * Other rules about < and <=                          *)
(**********************************************************)

Lemma Rplus_lt_0_compat : forall r1 r2, 0 < r1 -> 0 < r2 -> 0 < r1 + r2.
Proof.
  intros x y; intros; apply Rlt_trans with x;
    [ assumption
      | pattern x at 1 in |- *; rewrite <- (Rplus_0_r x); apply Rplus_lt_compat_l;
        assumption ].
Qed.

Lemma Rplus_le_lt_0_compat : forall r1 r2, 0 <= r1 -> 0 < r2 -> 0 < r1 + r2.
Proof.
  intros x y; intros; apply Rle_lt_trans with x;
    [ assumption
      | pattern x at 1 in |- *; rewrite <- (Rplus_0_r x); apply Rplus_lt_compat_l;
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
      | pattern x at 1 in |- *; rewrite <- (Rplus_0_r x); apply Rplus_le_compat_l;
        assumption ].
Qed.

Lemma plus_le_is_le : forall r1 r2 r3, 0 <= r2 -> r1 + r2 <= r3 -> r1 <= r3.
Proof.
  intros x y z; intros; apply Rle_trans with (x + y);
    [ pattern x at 1 in |- *; rewrite <- (Rplus_0_r x); apply Rplus_le_compat_l;
      assumption
      | assumption ].
Qed.

Lemma plus_lt_is_lt : forall r1 r2 r3, 0 <= r2 -> r1 + r2 < r3 -> r1 < r3.
Proof.
  intros x y z; intros; apply Rle_lt_trans with (x + y);
    [ pattern x at 1 in |- *; rewrite <- (Rplus_0_r x); apply Rplus_le_compat_l;
      assumption
      | assumption ].
Qed.

Lemma Rmult_le_0_lt_compat :
  forall r1 r2 r3 r4,
    0 <= r1 -> 0 <= r3 -> r1 < r2 -> r3 < r4 -> r1 * r3 < r2 * r4.
Proof.
  intros; apply Rle_lt_trans with (r2 * r3);
    [ apply Rmult_le_compat_r; [ assumption | left; assumption ]
      | apply Rmult_lt_compat_l;
        [ apply Rle_lt_trans with r1; assumption | assumption ] ].
Qed.

Lemma le_epsilon :
  forall r1 r2, (forall eps:R, 0 < eps -> r1 <= r2 + eps) -> r1 <= r2.
Proof.
  intros x y; intros; elim (Rtotal_order x y); intro.
  left; assumption.
  elim H0; intro.
  right; assumption.
  clear H0; generalize (Rgt_minus x y H1); intro H2; change (0 < x - y) in H2.
  cut (0 < 2).
  intro.
  generalize (Rmult_lt_0_compat (x - y) (/ 2) H2 (Rinv_0_lt_compat 2 H0));
    intro H3; generalize (H ((x - y) * / 2) H3);
      replace (y + (x - y) * / 2) with ((y + x) * / 2).
  intro H4;
    generalize (Rmult_le_compat_l 2 x ((y + x) * / 2) (Rlt_le 0 2 H0) H4);
      rewrite <- (Rmult_comm ((y + x) * / 2)); rewrite Rmult_assoc;
        rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; replace (2 * x) with (x + x).
  rewrite (Rplus_comm y); intro H5; apply Rplus_le_reg_l with x; assumption.
  ring. 
  replace 2 with (INR 2); [ apply not_O_INR; discriminate | reflexivity ].
  pattern y at 2 in |- *; replace y with (y / 2 + y / 2).
  unfold Rminus, Rdiv in |- *.
  repeat rewrite Rmult_plus_distr_r.
  ring.
  cut (forall z:R, 2 * z = z + z).
  intro.
  rewrite <- (H4 (y / 2)).
  unfold Rdiv in |- *.
  rewrite <- Rmult_assoc; apply Rinv_r_simpl_m.
  replace 2 with (INR 2).
  apply not_O_INR.
  discriminate.
  unfold INR in |- *; reflexivity.
  intro; ring.
  cut (0%nat <> 2%nat);
    [ intro H0; generalize (lt_INR_0 2 (neq_O_lt 2 H0)); unfold INR in |- *;
      intro; assumption
      | discriminate ].
Qed.

(**********)
Lemma completeness_weak :
  forall E:R -> Prop,
    bound E -> (exists x : R, E x) ->  exists m : R, is_lub E m.
Proof.
  intros; elim (completeness E H H0); intros; split with x; assumption.
Qed.
