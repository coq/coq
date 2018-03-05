(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i Some properties about pow and sum have been made with John Harrison i*)
(*i Some Lemmas (about pow and powerRZ) have been done by Laurent Thery i*)

(********************************************************)
(**          Definition of the sum functions            *)
(*                                                      *)
(********************************************************)
Require Export ArithRing.

Require Import Rbase.
Require Export Rpow_def.
Require Export R_Ifp.
Require Export Rbasic_fun.
Require Export R_sqr.
Require Export SplitAbsolu.
Require Export SplitRmult.
Require Export ArithProp.
Require Import Omega.
Require Import Zpower.
Local Open Scope nat_scope.
Local Open Scope R_scope.

(*******************************)
(** * Lemmas about factorial   *)
(*******************************)
(*********)
Lemma INR_fact_neq_0 : forall n:nat, INR (fact n) <> 0.
Proof.
  intro; red; intro; apply (not_O_INR (fact n) (fact_neq_0 n));
    assumption.
Qed.

(*********)
Lemma fact_simpl : forall n:nat, fact (S n) = (S n * fact n)%nat.
Proof.
  intro; reflexivity.
Qed.

(*********)
Lemma simpl_fact :
  forall n:nat, / INR (fact (S n)) * / / INR (fact n) = / INR (S n).
Proof.
  intro; rewrite (Rinv_involutive (INR (fact n)) (INR_fact_neq_0 n));
    unfold fact at 1; cbv beta iota; fold fact;
      rewrite (mult_INR (S n) (fact n));
        rewrite (Rinv_mult_distr (INR (S n)) (INR (fact n))).
  rewrite (Rmult_assoc (/ INR (S n)) (/ INR (fact n)) (INR (fact n)));
    rewrite (Rinv_l (INR (fact n)) (INR_fact_neq_0 n));
      apply (let (H1, H2) := Rmult_ne (/ INR (S n)) in H1).
  apply not_O_INR; auto.
  apply INR_fact_neq_0.
Qed.

(*******************************)
(** *       Power              *)
(*******************************)
(*********)

Infix "^" := pow : R_scope.

Lemma pow_O : forall x:R, x ^ 0 = 1.
Proof.
  reflexivity.
Qed.

Lemma pow_1 : forall x:R, x ^ 1 = x.
Proof.
  simpl; auto with real.
Qed.

Lemma pow_add : forall (x:R) (n m:nat), x ^ (n + m) = x ^ n * x ^ m.
Proof.
  intros x n; elim n; simpl; auto with real.
  intros n0 H' m; rewrite H'; auto with real.
Qed.

Lemma Rpow_mult_distr : forall (x y:R) (n:nat), (x * y) ^ n = x^n * y^n.
Proof.
intros x y n ; induction n.
 field.
 simpl.
 repeat (rewrite Rmult_assoc) ; apply Rmult_eq_compat_l.
 rewrite IHn ; field.
Qed.

Lemma pow_nonzero : forall (x:R) (n:nat), x <> 0 -> x ^ n <> 0.
Proof.
  intro; simple induction n; simpl.
  intro; red; intro; apply R1_neq_R0; assumption.
  intros; red; intro; elim (Rmult_integral x (x ^ n0) H1).
  intro; auto.
  apply H; assumption.
Qed.

Hint Resolve pow_O pow_1 pow_add pow_nonzero: real.

Lemma pow_RN_plus :
  forall (x:R) (n m:nat), x <> 0 -> x ^ n = x ^ (n + m) * / x ^ m.
Proof.
  intros x n; elim n; simpl; auto with real.
  intros n0 H' m H'0.
  rewrite Rmult_assoc; rewrite <- H'; auto.
Qed.

Lemma pow_lt : forall (x:R) (n:nat), 0 < x -> 0 < x ^ n.
Proof.
  intros x n; elim n; simpl; auto with real.
  intros n0 H' H'0; replace 0 with (x * 0); auto with real.
Qed.
Hint Resolve pow_lt: real.

Lemma Rlt_pow_R1 : forall (x:R) (n:nat), 1 < x -> (0 < n)%nat -> 1 < x ^ n.
Proof.
  intros x n; elim n; simpl; auto with real.
  intros H' H'0; exfalso; omega.
  intros n0; case n0.
  simpl; rewrite Rmult_1_r; auto.
  intros n1 H' H'0 H'1.
  replace 1 with (1 * 1); auto with real.
  apply Rlt_trans with (r2 := x * 1); auto with real.
  apply Rmult_lt_compat_l; auto with real.
  apply Rlt_trans with (r2 := 1); auto with real.
  apply H'; auto with arith.
Qed.
Hint Resolve Rlt_pow_R1: real.

Lemma Rlt_pow : forall (x:R) (n m:nat), 1 < x -> (n < m)%nat -> x ^ n < x ^ m.
Proof.
  intros x n m H' H'0; replace m with (m - n + n)%nat.
  rewrite pow_add.
  pattern (x ^ n) at 1; replace (x ^ n) with (1 * x ^ n);
    auto with real.
  apply Rminus_lt.
  repeat rewrite (fun y:R => Rmult_comm y (x ^ n));
    rewrite <- Rmult_minus_distr_l.
  replace 0 with (x ^ n * 0); auto with real.
  apply Rmult_lt_compat_l; auto with real.
  apply pow_lt; auto with real.
  apply Rlt_trans with (r2 := 1); auto with real.
  apply Rlt_minus; auto with real.
  apply Rlt_pow_R1; auto with arith.
  apply plus_lt_reg_l with (p := n); auto with arith.
  rewrite le_plus_minus_r; auto with arith; rewrite <- plus_n_O; auto.
  rewrite plus_comm; auto with arith.
Qed.
Hint Resolve Rlt_pow: real.

(*********)
Lemma tech_pow_Rmult : forall (x:R) (n:nat), x * x ^ n = x ^ S n.
Proof.
  simple induction n; simpl; trivial.
Qed.

(*********)
Lemma tech_pow_Rplus :
  forall (x:R) (a n:nat), x ^ a + INR n * x ^ a = INR (S n) * x ^ a.
Proof.
  intros; pattern (x ^ a) at 1;
    rewrite <- (let (H1, H2) := Rmult_ne (x ^ a) in H1);
      rewrite (Rmult_comm (INR n) (x ^ a));
        rewrite <- (Rmult_plus_distr_l (x ^ a) 1 (INR n));
          rewrite (Rplus_comm 1 (INR n)); rewrite <- (S_INR n);
            apply Rmult_comm.
Qed.

Lemma poly : forall (n:nat) (x:R), 0 < x -> 1 + INR n * x <= (1 + x) ^ n.
Proof.
  intros; elim n.
  simpl; cut (1 + 0 * x = 1).
  intro; rewrite H0; unfold Rle; right; reflexivity.
  ring.
  intros; unfold pow; fold pow;
    apply
      (Rle_trans (1 + INR (S n0) * x) ((1 + x) * (1 + INR n0 * x))
        ((1 + x) * (1 + x) ^ n0)).
  cut ((1 + x) * (1 + INR n0 * x) = 1 + INR (S n0) * x + INR n0 * (x * x)).
  intro; rewrite H1; pattern (1 + INR (S n0) * x) at 1;
    rewrite <- (let (H1, H2) := Rplus_ne (1 + INR (S n0) * x) in H1);
      apply Rplus_le_compat_l; elim n0; intros.
  simpl; rewrite Rmult_0_l; unfold Rle; right; auto.
  unfold Rle; left; generalize Rmult_gt_0_compat; unfold Rgt;
    intro; fold (Rsqr x);
      apply (H3 (INR (S n1)) (Rsqr x) (lt_INR_0 (S n1) (lt_O_Sn n1)));
        fold (x > 0) in H;
          apply (Rlt_0_sqr x (Rlt_dichotomy_converse x 0 (or_intror (x < 0) H))).
  rewrite (S_INR n0); ring.
  unfold Rle in H0; elim H0; intro.
  unfold Rle; left; apply Rmult_lt_compat_l.
  rewrite Rplus_comm; apply (Rle_lt_0_plus_1 x (Rlt_le 0 x H)).
  assumption.
  rewrite H1; unfold Rle; right; trivial.
Qed.

Lemma Power_monotonic :
  forall (x:R) (m n:nat),
    Rabs x > 1 -> (m <= n)%nat -> Rabs (x ^ m) <= Rabs (x ^ n).
Proof.
  intros x m n H; induction  n as [| n Hrecn]; intros; inversion H0.
  unfold Rle; right; reflexivity.
  unfold Rle; right; reflexivity.
  apply (Rle_trans (Rabs (x ^ m)) (Rabs (x ^ n)) (Rabs (x ^ S n))).
  apply Hrecn; assumption.
  simpl; rewrite Rabs_mult.
  pattern (Rabs (x ^ n)) at 1.
  rewrite <- Rmult_1_r.
  rewrite (Rmult_comm (Rabs x) (Rabs (x ^ n))).
  apply Rmult_le_compat_l.
  apply Rabs_pos.
  unfold Rgt in H.
  apply Rlt_le; assumption.
Qed.

Lemma RPow_abs : forall (x:R) (n:nat), Rabs x ^ n = Rabs (x ^ n).
Proof.
  intro; simple induction n; simpl.
  symmetry; apply Rabs_pos_eq; apply Rlt_le; apply Rlt_0_1.
  intros; rewrite H; symmetry; apply Rabs_mult.
Qed.


Lemma Pow_x_infinity :
  forall x:R,
    Rabs x > 1 ->
    forall b:R,
      exists N : nat, (forall n:nat, (n >= N)%nat -> Rabs (x ^ n) >= b).
Proof.
  intros; elim (archimed (b * / (Rabs x - 1))); intros; clear H1;
    cut (exists N : nat, INR N >= b * / (Rabs x - 1)).
  intro; elim H1; clear H1; intros; exists x0; intros;
    apply (Rge_trans (Rabs (x ^ n)) (Rabs (x ^ x0)) b).
  apply Rle_ge; apply Power_monotonic; assumption.
  rewrite <- RPow_abs; cut (Rabs x = 1 + (Rabs x - 1)).
  intro; rewrite H3;
    apply (Rge_trans ((1 + (Rabs x - 1)) ^ x0) (1 + INR x0 * (Rabs x - 1)) b).
  apply Rle_ge; apply poly; fold (Rabs x - 1 > 0); apply Rgt_minus;
    assumption.
  apply (Rge_trans (1 + INR x0 * (Rabs x - 1)) (INR x0 * (Rabs x - 1)) b).
  apply Rle_ge; apply Rlt_le; rewrite (Rplus_comm 1 (INR x0 * (Rabs x - 1)));
    pattern (INR x0 * (Rabs x - 1)) at 1;
      rewrite <- (let (H1, H2) := Rplus_ne (INR x0 * (Rabs x - 1)) in H1);
        apply Rplus_lt_compat_l; apply Rlt_0_1.
  cut (b = b * / (Rabs x - 1) * (Rabs x - 1)).
  intros; rewrite H4; apply Rmult_ge_compat_r.
  apply Rge_minus; unfold Rge; left; assumption.
  assumption.
  rewrite Rmult_assoc; rewrite Rinv_l.
  ring.
  apply Rlt_dichotomy_converse; right; apply Rgt_minus; assumption.
  ring.
  cut ((0 <= up (b * / (Rabs x - 1)))%Z \/ (up (b * / (Rabs x - 1)) <= 0)%Z).
  intros; elim H1; intro.
  elim (IZN (up (b * / (Rabs x - 1))) H2); intros; exists x0;
    apply
      (Rge_trans (INR x0) (IZR (up (b * / (Rabs x - 1)))) (b * / (Rabs x - 1))).
  rewrite INR_IZR_INZ; apply IZR_ge; omega.
  unfold Rge; left; assumption.
  exists 0%nat;
    apply
      (Rge_trans (INR 0) (IZR (up (b * / (Rabs x - 1)))) (b * / (Rabs x - 1))).
  rewrite INR_IZR_INZ; apply IZR_ge; simpl; omega.
  unfold Rge; left; assumption.
  omega.
Qed.

Lemma pow_ne_zero : forall n:nat, n <> 0%nat -> 0 ^ n = 0.
Proof.
  simple induction n.
  simpl; auto.
  intros; elim H; reflexivity.
  intros; simpl; apply Rmult_0_l.
Qed.

Lemma Rinv_pow : forall (x:R) (n:nat), x <> 0 -> / x ^ n = (/ x) ^ n.
Proof.
  intros; elim n; simpl.
  apply Rinv_1.
  intro m; intro; rewrite Rinv_mult_distr.
  rewrite H0; reflexivity; assumption.
  assumption.
  apply pow_nonzero; assumption.
Qed.

Lemma pow_lt_1_zero :
  forall x:R,
    Rabs x < 1 ->
    forall y:R,
      0 < y ->
      exists N : nat, (forall n:nat, (n >= N)%nat -> Rabs (x ^ n) < y).
Proof.
  intros; elim (Req_dec x 0); intro.
  exists 1%nat; rewrite H1; intros n GE; rewrite pow_ne_zero.
  rewrite Rabs_R0; assumption.
  inversion GE; auto.
  cut (Rabs (/ x) > 1).
  intros; elim (Pow_x_infinity (/ x) H2 (/ y + 1)); intros N.
  exists N; intros; rewrite <- (Rinv_involutive y).
  rewrite <- (Rinv_involutive (Rabs (x ^ n))).
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat.
  apply Rinv_0_lt_compat.
  assumption.
  apply Rinv_0_lt_compat.
  apply Rabs_pos_lt.
  apply pow_nonzero.
  assumption.
  rewrite <- Rabs_Rinv.
  rewrite Rinv_pow.
  apply (Rlt_le_trans (/ y) (/ y + 1) (Rabs ((/ x) ^ n))).
  pattern (/ y) at 1.
  rewrite <- (let (H1, H2) := Rplus_ne (/ y) in H1).
  apply Rplus_lt_compat_l.
  apply Rlt_0_1.
  apply Rge_le.
  apply H3.
  assumption.
  assumption.
  apply pow_nonzero.
  assumption.
  apply Rabs_no_R0.
  apply pow_nonzero.
  assumption.
  apply Rlt_dichotomy_converse.
  right; unfold Rgt; assumption.
  rewrite <- (Rinv_involutive 1).
  rewrite Rabs_Rinv.
  unfold Rgt; apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat.
  apply Rabs_pos_lt.
  assumption.
  rewrite Rinv_1; apply Rlt_0_1.
  rewrite Rinv_1; assumption.
  assumption.
  red; intro; apply R1_neq_R0; assumption.
Qed.

Lemma pow_R1 : forall (r:R) (n:nat), r ^ n = 1 -> Rabs r = 1 \/ n = 0%nat.
Proof.
  intros r n H'.
  case (Req_dec (Rabs r) 1); auto; intros H'1.
  case (Rdichotomy _ _ H'1); intros H'2.
  generalize H'; case n; auto.
  intros n0 H'0.
  cut (r <> 0); [ intros Eq1 | idtac ].
  cut (Rabs r <> 0); [ intros Eq2 | apply Rabs_no_R0 ]; auto.
  absurd (Rabs (/ r) ^ 0 < Rabs (/ r) ^ S n0); auto.
  replace (Rabs (/ r) ^ S n0) with 1.
  simpl; apply Rlt_irrefl; auto.
  rewrite Rabs_Rinv; auto.
  rewrite <- Rinv_pow; auto.
  rewrite RPow_abs; auto.
  rewrite H'0; rewrite Rabs_right; auto with real rorders.
  apply Rlt_pow; auto with arith.
  rewrite Rabs_Rinv; auto.
  apply Rmult_lt_reg_l with (r := Rabs r).
  case (Rabs_pos r); auto.
  intros H'3; case Eq2; auto.
  rewrite Rmult_1_r; rewrite Rinv_r; auto with real.
  red; intro; absurd (r ^ S n0 = 1); auto.
  simpl; rewrite H; rewrite Rmult_0_l; auto with real.
  generalize H'; case n; auto.
  intros n0 H'0.
  cut (r <> 0); [ intros Eq1 | auto with real ].
  cut (Rabs r <> 0); [ intros Eq2 | apply Rabs_no_R0 ]; auto.
  absurd (Rabs r ^ 0 < Rabs r ^ S n0); auto with real arith.
  repeat rewrite RPow_abs; rewrite H'0; simpl; auto with real.
  red; intro; absurd (r ^ S n0 = 1); auto.
  simpl; rewrite H; rewrite Rmult_0_l; auto with real.
Qed.

Lemma pow_Rsqr : forall (x:R) (n:nat), x ^ (2 * n) = Rsqr x ^ n.
Proof.
  intros; induction  n as [| n Hrecn].
  reflexivity.
  replace (2 * S n)%nat with (S (S (2 * n))).
  replace (x ^ S (S (2 * n))) with (x * x * x ^ (2 * n)).
  rewrite Hrecn; reflexivity.
  simpl; ring.
  ring.
Qed.

Lemma pow_le : forall (a:R) (n:nat), 0 <= a -> 0 <= a ^ n.
Proof.
  intros; induction  n as [| n Hrecn].
  simpl; left; apply Rlt_0_1.
  simpl; apply Rmult_le_pos; assumption.
Qed.

(**********)
Lemma pow_1_even : forall n:nat, (-1) ^ (2 * n) = 1.
Proof.
  intro; induction  n as [| n Hrecn].
  reflexivity.
  replace (2 * S n)%nat with (2 + 2 * n)%nat by ring.
  rewrite pow_add; rewrite Hrecn; simpl; ring.
Qed.

(**********)
Lemma pow_1_odd : forall n:nat, (-1) ^ S (2 * n) = -1.
Proof.
  intro; replace (S (2 * n)) with (2 * n + 1)%nat by ring.
  rewrite pow_add; rewrite pow_1_even; simpl; ring.
Qed.

(**********)
Lemma pow_1_abs : forall n:nat, Rabs ((-1) ^ n) = 1.
Proof.
  intro; induction  n as [| n Hrecn].
  simpl; apply Rabs_R1.
  replace (S n) with (n + 1)%nat; [ rewrite pow_add | ring ].
  rewrite Rabs_mult.
  rewrite Hrecn; rewrite Rmult_1_l; simpl; rewrite Rmult_1_r.
  change (-1) with (-(1)).
  rewrite Rabs_Ropp; apply Rabs_R1.
Qed.

Lemma pow_mult : forall (x:R) (n1 n2:nat), x ^ (n1 * n2) = (x ^ n1) ^ n2.
Proof.
  intros; induction  n2 as [| n2 Hrecn2].
  simpl; replace (n1 * 0)%nat with 0%nat; [ reflexivity | ring ].
  replace (n1 * S n2)%nat with (n1 * n2 + n1)%nat.
  replace (S n2) with (n2 + 1)%nat by ring.
  do 2 rewrite pow_add.
  rewrite Hrecn2.
  simpl.
  ring.
  ring.
Qed.

Lemma pow_incr : forall (x y:R) (n:nat), 0 <= x <= y -> x ^ n <= y ^ n.
Proof.
  intros.
  induction  n as [| n Hrecn].
  right; reflexivity.
  simpl.
  elim H; intros.
  apply Rle_trans with (y * x ^ n).
  do 2 rewrite <- (Rmult_comm (x ^ n)).
  apply Rmult_le_compat_l.
  apply pow_le; assumption.
  assumption.
  apply Rmult_le_compat_l.
  apply Rle_trans with x; assumption.
  apply Hrecn.
Qed.

Lemma pow_R1_Rle : forall (x:R) (k:nat), 1 <= x -> 1 <= x ^ k.
Proof.
  intros.
  induction  k as [| k Hreck].
  right; reflexivity.
  simpl.
  apply Rle_trans with (x * 1).
  rewrite Rmult_1_r; assumption.
  apply Rmult_le_compat_l.
  left; apply Rlt_le_trans with 1; [ apply Rlt_0_1 | assumption ].
  exact Hreck.
Qed.

Lemma Rle_pow :
  forall (x:R) (m n:nat), 1 <= x -> (m <= n)%nat -> x ^ m <= x ^ n.
Proof.
  intros.
  replace n with (n - m + m)%nat.
  rewrite pow_add.
  rewrite Rmult_comm.
  pattern (x ^ m) at 1; rewrite <- Rmult_1_r.
  apply Rmult_le_compat_l.
  apply pow_le; left; apply Rlt_le_trans with 1; [ apply Rlt_0_1 | assumption ].
  apply pow_R1_Rle; assumption.
  rewrite plus_comm.
  symmetry ; apply le_plus_minus; assumption.
Qed.

Lemma pow1 : forall n:nat, 1 ^ n = 1.
Proof.
  intro; induction  n as [| n Hrecn].
  reflexivity.
  simpl; rewrite Hrecn; rewrite Rmult_1_r; reflexivity.
Qed.

Lemma pow_Rabs : forall (x:R) (n:nat), x ^ n <= Rabs x ^ n.
Proof.
  intros; induction  n as [| n Hrecn].
  right; reflexivity.
  simpl; destruct (Rcase_abs x) as [Hlt|Hle].
  apply Rle_trans with (Rabs (x * x ^ n)).
  apply RRle_abs.
  rewrite Rabs_mult.
  apply Rmult_le_compat_l.
  apply Rabs_pos.
  right; symmetry; apply RPow_abs.
  pattern (Rabs x) at 1; rewrite (Rabs_right x Hle);
    apply Rmult_le_compat_l.
  apply Rge_le; exact Hle.
  apply Hrecn.
Qed.

Lemma pow_maj_Rabs : forall (x y:R) (n:nat), Rabs y <= x -> y ^ n <= x ^ n.
Proof.
  intros; cut (0 <= x).
  intro; apply Rle_trans with (Rabs y ^ n).
  apply pow_Rabs.
  induction  n as [| n Hrecn].
  right; reflexivity.
  simpl; apply Rle_trans with (x * Rabs y ^ n).
  do 2 rewrite <- (Rmult_comm (Rabs y ^ n)).
  apply Rmult_le_compat_l.
  apply pow_le; apply Rabs_pos.
  assumption.
  apply Rmult_le_compat_l.
  apply H0.
  apply Hrecn.
  apply Rle_trans with (Rabs y); [ apply Rabs_pos | exact H ].
Qed.

Lemma Rsqr_pow2 : forall x, Rsqr x = x ^ 2.
Proof.
intros; unfold Rsqr; simpl; rewrite Rmult_1_r; reflexivity.
Qed.


(*******************************)
(** *       PowerRZ            *)
(*******************************)
(*i Due to L.Thery i*)

Section PowerRZ.

Local Coercion Z_of_nat : nat >-> Z.

(* the following section should probably be somewhere else, but not sure where *)
Section Z_compl.

Local Open Scope Z_scope.

(* Provides a way to reason directly on Z in terms of nats instead of positive *)
Inductive Z_spec (x : Z) : Z -> Type :=
| ZintNull : x = 0 -> Z_spec x 0
| ZintPos (n : nat) : x = n -> Z_spec x n
| ZintNeg (n : nat) : x = - n -> Z_spec x (- n).

Lemma intP (x : Z) : Z_spec x x.
Proof.
  destruct x as [|p|p].
  - now apply ZintNull.
  - rewrite <-positive_nat_Z at 2.
    apply ZintPos.
    now rewrite positive_nat_Z.
  - rewrite <-Pos2Z.opp_pos.
    rewrite <-positive_nat_Z at 2.
    apply ZintNeg.
    now rewrite positive_nat_Z.
Qed.

End Z_compl.

Definition powerRZ (x:R) (n:Z) :=
  match n with
    | Z0 => 1
    | Zpos p => x ^ Pos.to_nat p
    | Zneg p => / x ^ Pos.to_nat p
  end.

Local Infix "^Z" := powerRZ (at level 30, right associativity) : R_scope.

Lemma Zpower_NR0 :
  forall (x:Z) (n:nat), (0 <= x)%Z -> (0 <= Zpower_nat x n)%Z.
Proof.
  induction n; unfold Zpower_nat; simpl; auto with zarith.
Qed.

Lemma powerRZ_O : forall x:R, x ^Z 0 = 1.
Proof.
  reflexivity.
Qed.

Lemma powerRZ_1 : forall x:R, x ^Z Z.succ 0 = x.
Proof.
  simpl; auto with real.
Qed.

Lemma powerRZ_NOR : forall (x:R) (z:Z), x <> 0 -> x ^Z z <> 0.
Proof.
  destruct z; simpl; auto with real.
Qed.

Lemma powerRZ_pos_sub (x:R) (n m:positive) : x <> 0 ->
   x ^Z (Z.pos_sub n m) = x ^ Pos.to_nat n * / x ^ Pos.to_nat m.
Proof.
 intro Hx.
 rewrite Z.pos_sub_spec.
 case Pos.compare_spec; intro H; simpl.
 - subst; auto with real.
 - rewrite Pos2Nat.inj_sub by trivial.
   rewrite Pos2Nat.inj_lt in H.
   rewrite (pow_RN_plus x _ (Pos.to_nat n)) by auto with real.
   rewrite plus_comm, le_plus_minus_r by auto with real.
   rewrite Rinv_mult_distr, Rinv_involutive; auto with real.
 - rewrite Pos2Nat.inj_sub by trivial.
   rewrite Pos2Nat.inj_lt in H.
   rewrite (pow_RN_plus x _ (Pos.to_nat m)) by auto with real.
   rewrite plus_comm, le_plus_minus_r by auto with real.
   reflexivity.
Qed.

Lemma powerRZ_add :
  forall (x:R) (n m:Z), x <> 0 -> x ^Z (n + m) = x ^Z n * x ^Z m.
Proof.
  intros x [|n|n] [|m|m]; simpl; intros; auto with real.
  - (* + + *)
    rewrite Pos2Nat.inj_add; auto with real.
  - (* + - *)
    now apply powerRZ_pos_sub.
  - (* - + *)
    rewrite Rmult_comm. now apply powerRZ_pos_sub.
  - (* - - *)
    rewrite Pos2Nat.inj_add; auto with real.
    rewrite pow_add; auto with real.
    apply Rinv_mult_distr; apply pow_nonzero; auto.
Qed.
Hint Resolve powerRZ_O powerRZ_1 powerRZ_NOR powerRZ_add: real.

Lemma Zpower_nat_powerRZ :
  forall n m:nat, IZR (Zpower_nat (Z.of_nat n) m) = INR n ^Z Z.of_nat m.
Proof.
  intros n m; elim m; simpl; auto with real.
  intros m1 H'; rewrite SuccNat2Pos.id_succ; simpl.
  replace (Zpower_nat (Z.of_nat n) (S m1)) with
  (Z.of_nat n * Zpower_nat (Z.of_nat n) m1)%Z.
  rewrite mult_IZR; auto with real.
  repeat rewrite <- INR_IZR_INZ; simpl.
  rewrite H'; simpl.
  case m1; simpl; auto with real.
  intros m2; rewrite SuccNat2Pos.id_succ; auto.
  unfold Zpower_nat; auto.
Qed.

Lemma Zpower_pos_powerRZ :
  forall n m, IZR (Z.pow_pos n m) = IZR n ^Z Zpos m.
Proof.
  intros.
  rewrite Zpower_pos_nat; simpl.
  induction (Pos.to_nat m).
  easy.
  unfold Zpower_nat; simpl.
  rewrite mult_IZR.
  now rewrite <- IHn0.
Qed.

Lemma powerRZ_lt : forall (x:R) (z:Z), 0 < x -> 0 < x ^Z z.
Proof.
  intros x z; case z; simpl; auto with real.
Qed.
Hint Resolve powerRZ_lt: real.

Lemma powerRZ_le : forall (x:R) (z:Z), 0 < x -> 0 <= x ^Z z.
Proof.
  intros x z H'; apply Rlt_le; auto with real.
Qed.
Hint Resolve powerRZ_le: real.

Lemma Zpower_nat_powerRZ_absolu :
  forall n m:Z, (0 <= m)%Z -> IZR (Zpower_nat n (Z.abs_nat m)) = IZR n ^Z m.
Proof.
  intros n m; case m; simpl; auto with zarith.
  intros p H'; elim (Pos.to_nat p); simpl; auto with zarith.
  intros n0 H'0; rewrite <- H'0; simpl; auto with zarith.
  rewrite <- mult_IZR; auto.
  intros p H'; absurd (0 <= Zneg p)%Z; auto with zarith.
Qed.

Lemma powerRZ_R1 : forall n:Z, 1 ^Z n = 1.
Proof.
  intros n; case n; simpl; auto.
  intros p; elim (Pos.to_nat p); simpl; auto; intros n0 H'; rewrite H';
    ring.
  intros p; elim (Pos.to_nat p); simpl.
  exact Rinv_1.
  intros n1 H'; rewrite Rinv_mult_distr; try rewrite Rinv_1; try rewrite H';
    auto with real.
Qed.

Local Open Scope Z_scope.

Lemma pow_powerRZ (r : R) (n : nat) :
  (r ^ n)%R = powerRZ r (Z_of_nat n).
Proof.
  induction n; [easy|simpl].
  now rewrite SuccNat2Pos.id_succ.
Qed.

Lemma powerRZ_ind (P : Z -> R -> R -> Prop) :
  (forall x, P 0 x 1%R) ->
  (forall x n, P (Z.of_nat n) x (x ^ n)%R) ->
  (forall x n, P ((-(Z.of_nat n))%Z) x (Rinv (x ^ n))) ->
  forall x (m : Z), P m x (powerRZ x m)%R.
Proof.
  intros ? ? ? x m.
  destruct (intP m) as [Hm|n Hm|n Hm].
  - easy.
  - now rewrite <- pow_powerRZ.
  - unfold powerRZ.
    destruct n as [|n]; [ easy |].
    rewrite Nat2Z.inj_succ, <- Zpos_P_of_succ_nat, Pos2Z.opp_pos.
    now rewrite <- Pos2Z.opp_pos, <- positive_nat_Z.
Qed.

Lemma powerRZ_inv x alpha : (x <> 0)%R -> powerRZ (/ x) alpha = Rinv (powerRZ x alpha).
Proof.
  intros; destruct (intP alpha).
  - now simpl; rewrite Rinv_1.
  - now rewrite <-!pow_powerRZ, ?Rinv_pow, ?pow_powerRZ.
  - unfold powerRZ.
    destruct (- n).
    + now rewrite Rinv_1.
    + now rewrite Rinv_pow.
    + now rewrite <-Rinv_pow.
Qed.

Lemma powerRZ_neg x : forall alpha, x <> R0 -> powerRZ x (- alpha) = powerRZ (/ x) alpha.
Proof.
  intros [|n|n] H ; simpl.
  - easy.
  - now rewrite Rinv_pow.
  - rewrite Rinv_pow by now apply Rinv_neq_0_compat.
    now rewrite Rinv_involutive.
Qed.

Lemma powerRZ_mult_distr :
  forall m x y, ((0 <= m)%Z \/ (x * y <> 0)%R) ->
           (powerRZ (x*y) m = powerRZ x m * powerRZ y m)%R.
Proof.
  intros m x0 y0 Hmxy.
  destruct (intP m) as [ | | n Hm ].
  - now simpl; rewrite Rmult_1_l.
  - now rewrite <- !pow_powerRZ, Rpow_mult_distr.
  - destruct Hmxy as [H|H].
    + assert(m = 0) as -> by now omega.
      now rewrite <- Hm, Rmult_1_l.
    + assert(x0 <> 0)%R by now intros ->; apply H; rewrite Rmult_0_l.
      assert(y0 <> 0)%R by now intros ->; apply H; rewrite Rmult_0_r.
      rewrite !powerRZ_neg by assumption.
      rewrite Rinv_mult_distr by assumption.
      now rewrite <- !pow_powerRZ, Rpow_mult_distr.
Qed.

End PowerRZ.

Local Infix "^Z" := powerRZ (at level 30, right associativity) : R_scope.

(*******************************)
(* For easy interface          *)
(*******************************)
(* decimal_exp r z is defined as r 10^z *)

Definition decimal_exp (r:R) (z:Z) : R := (r * 10 ^Z z).


(*******************************)
(** * Sum of n first naturals  *)
(*******************************)
(*********)
Fixpoint sum_nat_f_O (f:nat -> nat) (n:nat) : nat :=
  match n with
    | O => f 0%nat
    | S n' => (sum_nat_f_O f n' + f (S n'))%nat
  end.

(*********)
Definition sum_nat_f (s n:nat) (f:nat -> nat) : nat :=
  sum_nat_f_O (fun x:nat => f (x + s)%nat) (n - s).

(*********)
Definition sum_nat_O (n:nat) : nat := sum_nat_f_O (fun x:nat => x) n.

(*********)
Definition sum_nat (s n:nat) : nat := sum_nat_f s n (fun x:nat => x).

(*******************************)
(** *          Sum             *)
(*******************************)
(*********)
Fixpoint sum_f_R0 (f:nat -> R) (N:nat) : R :=
  match N with
    | O => f 0%nat
    | S i => sum_f_R0 f i + f (S i)
  end.

(*********)
Definition sum_f (s n:nat) (f:nat -> R) : R :=
  sum_f_R0 (fun x:nat => f (x + s)%nat) (n - s).

Lemma GP_finite :
  forall (x:R) (n:nat),
    sum_f_R0 (fun n:nat => x ^ n) n * (x - 1) = x ^ (n + 1) - 1.
Proof.
  intros; induction  n as [| n Hrecn]; simpl.
  ring.
  rewrite Rmult_plus_distr_r; rewrite Hrecn; cut ((n + 1)%nat = S n).
  intro H; rewrite H; simpl; ring.
  omega.
Qed.

Lemma sum_f_R0_triangle :
  forall (x:nat -> R) (n:nat),
    Rabs (sum_f_R0 x n) <= sum_f_R0 (fun i:nat => Rabs (x i)) n.
Proof.
  intro; simple induction n; simpl.
  unfold Rle; right; reflexivity.
  intro m; intro;
    apply
      (Rle_trans (Rabs (sum_f_R0 x m + x (S m)))
        (Rabs (sum_f_R0 x m) + Rabs (x (S m)))
        (sum_f_R0 (fun i:nat => Rabs (x i)) m + Rabs (x (S m)))).
  apply Rabs_triang.
  rewrite Rplus_comm;
    rewrite (Rplus_comm (sum_f_R0 (fun i:nat => Rabs (x i)) m) (Rabs (x (S m))));
      apply Rplus_le_compat_l; assumption.
Qed.

(*******************************)
(** *     Distance  in R       *)
(*******************************)

(*********)
Definition R_dist (x y:R) : R := Rabs (x - y).

(*********)
Lemma R_dist_pos : forall x y:R, R_dist x y >= 0.
Proof.
  intros; unfold R_dist; unfold Rabs; case (Rcase_abs (x - y));
    intro l.
  unfold Rge; left; apply (Ropp_gt_lt_0_contravar (x - y) l).
  trivial.
Qed.

(*********)
Lemma R_dist_sym : forall x y:R, R_dist x y = R_dist y x.
Proof.
  unfold R_dist; intros; split_Rabs; try ring.
  generalize (Ropp_gt_lt_0_contravar (y - x) Hlt0); intro;
    rewrite (Ropp_minus_distr y x) in H; generalize (Rlt_asym (x - y) 0 Hlt);
      intro; unfold Rgt in H; exfalso; auto.
  generalize (minus_Rge y x Hge0); intro; generalize (minus_Rge x y Hge); intro;
    generalize (Rge_antisym x y H0 H); intro; rewrite H1;
      ring.
Qed.

(*********)
Lemma R_dist_refl : forall x y:R, R_dist x y = 0 <-> x = y.
Proof.
  unfold R_dist; intros; split_Rabs; split; intros.
  rewrite (Ropp_minus_distr x y) in H; symmetry;
    apply (Rminus_diag_uniq y x H).
  rewrite (Ropp_minus_distr x y); generalize (eq_sym H); intro;
    apply (Rminus_diag_eq y x H0).
  apply (Rminus_diag_uniq x y H).
  apply (Rminus_diag_eq x y H).
Qed.

Lemma R_dist_eq : forall x:R, R_dist x x = 0.
Proof.
  unfold R_dist; intros; split_Rabs; intros; ring.
Qed.

(***********)
Lemma R_dist_tri : forall x y z:R, R_dist x y <= R_dist x z + R_dist z y.
Proof.
  intros; unfold R_dist; replace (x - y) with (x - z + (z - y));
    [ apply (Rabs_triang (x - z) (z - y)) | ring ].
Qed.

(*********)
Lemma R_dist_plus :
  forall a b c d:R, R_dist (a + c) (b + d) <= R_dist a b + R_dist c d.
Proof.
  intros; unfold R_dist;
    replace (a + c - (b + d)) with (a - b + (c - d)).
  exact (Rabs_triang (a - b) (c - d)).
  ring.
Qed.

Lemma R_dist_mult_l : forall a b c,
  R_dist (a * b) (a * c) = Rabs a * R_dist b c.
Proof.
unfold R_dist. 
intros a b c; rewrite <- Rmult_minus_distr_l, Rabs_mult; reflexivity.
Qed.

(*******************************)
(** *     Infinite Sum          *)
(*******************************)
(*********)
Definition infinite_sum (s:nat -> R) (l:R) : Prop :=
  forall eps:R,
    eps > 0 ->
    exists N : nat,
      (forall n:nat, (n >= N)%nat -> R_dist (sum_f_R0 s n) l < eps).

(** Compatibility with previous versions *)
Notation infinit_sum := infinite_sum (only parsing).
