(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

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
Open Local Scope nat_scope.
Open Local Scope R_scope.

(*******************************)
(** * Lemmas about factorial   *)
(*******************************)
(*********)
Lemma INR_fact_neq_0 : forall n:nat, INR (fact n) <> 0.
Proof.
  intro; red in |- *; intro; apply (not_O_INR (fact n) (fact_neq_0 n));
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
    unfold fact at 1 in |- *; cbv beta iota in |- *; fold fact in |- *;
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
  simpl in |- *; auto with real.
Qed.

Lemma pow_add : forall (x:R) (n m:nat), x ^ (n + m) = x ^ n * x ^ m.
Proof.
  intros x n; elim n; simpl in |- *; auto with real.
  intros n0 H' m; rewrite H'; auto with real.
Qed.

Lemma pow_nonzero : forall (x:R) (n:nat), x <> 0 -> x ^ n <> 0.
Proof.
  intro; simple induction n; simpl in |- *.
  intro; red in |- *; intro; apply R1_neq_R0; assumption.
  intros; red in |- *; intro; elim (Rmult_integral x (x ^ n0) H1).
  intro; auto.
  apply H; assumption.
Qed.

Hint Resolve pow_O pow_1 pow_add pow_nonzero: real.

Lemma pow_RN_plus :
  forall (x:R) (n m:nat), x <> 0 -> x ^ n = x ^ (n + m) * / x ^ m.
Proof.
  intros x n; elim n; simpl in |- *; auto with real.
  intros n0 H' m H'0.
  rewrite Rmult_assoc; rewrite <- H'; auto.
Qed.

Lemma pow_lt : forall (x:R) (n:nat), 0 < x -> 0 < x ^ n.
Proof.
  intros x n; elim n; simpl in |- *; auto with real.
  intros n0 H' H'0; replace 0 with (x * 0); auto with real.
Qed.
Hint Resolve pow_lt: real.

Lemma Rlt_pow_R1 : forall (x:R) (n:nat), 1 < x -> (0 < n)%nat -> 1 < x ^ n.
Proof.
  intros x n; elim n; simpl in |- *; auto with real.
  intros H' H'0; elimtype False; omega.
  intros n0; case n0.
  simpl in |- *; rewrite Rmult_1_r; auto.
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
  pattern (x ^ n) at 1 in |- *; replace (x ^ n) with (1 * x ^ n);
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
  simple induction n; simpl in |- *; trivial.
Qed.

(*********)
Lemma tech_pow_Rplus :
  forall (x:R) (a n:nat), x ^ a + INR n * x ^ a = INR (S n) * x ^ a.
Proof.
  intros; pattern (x ^ a) at 1 in |- *;
    rewrite <- (let (H1, H2) := Rmult_ne (x ^ a) in H1);
      rewrite (Rmult_comm (INR n) (x ^ a));
        rewrite <- (Rmult_plus_distr_l (x ^ a) 1 (INR n));
          rewrite (Rplus_comm 1 (INR n)); rewrite <- (S_INR n); 
            apply Rmult_comm.
Qed.

Lemma poly : forall (n:nat) (x:R), 0 < x -> 1 + INR n * x <= (1 + x) ^ n.
Proof.
  intros; elim n.
  simpl in |- *; cut (1 + 0 * x = 1).
  intro; rewrite H0; unfold Rle in |- *; right; reflexivity.
  ring.
  intros; unfold pow in |- *; fold pow in |- *;
    apply
      (Rle_trans (1 + INR (S n0) * x) ((1 + x) * (1 + INR n0 * x))
        ((1 + x) * (1 + x) ^ n0)).
  cut ((1 + x) * (1 + INR n0 * x) = 1 + INR (S n0) * x + INR n0 * (x * x)).
  intro; rewrite H1; pattern (1 + INR (S n0) * x) at 1 in |- *;
    rewrite <- (let (H1, H2) := Rplus_ne (1 + INR (S n0) * x) in H1);
      apply Rplus_le_compat_l; elim n0; intros.
  simpl in |- *; rewrite Rmult_0_l; unfold Rle in |- *; right; auto.
  unfold Rle in |- *; left; generalize Rmult_gt_0_compat; unfold Rgt in |- *;
    intro; fold (Rsqr x) in |- *;
      apply (H3 (INR (S n1)) (Rsqr x) (lt_INR_0 (S n1) (lt_O_Sn n1)));
        fold (x > 0) in H;
          apply (Rlt_0_sqr x (Rlt_dichotomy_converse x 0 (or_intror (x < 0) H))).
  rewrite (S_INR n0); ring.
  unfold Rle in H0; elim H0; intro. 
  unfold Rle in |- *; left; apply Rmult_lt_compat_l.
  rewrite Rplus_comm; apply (Rle_lt_0_plus_1 x (Rlt_le 0 x H)).
  assumption.
  rewrite H1; unfold Rle in |- *; right; trivial.
Qed.

Lemma Power_monotonic :
  forall (x:R) (m n:nat),
    Rabs x > 1 -> (m <= n)%nat -> Rabs (x ^ m) <= Rabs (x ^ n).
Proof.
  intros x m n H; induction  n as [| n Hrecn]; intros; inversion H0.
  unfold Rle in |- *; right; reflexivity.
  unfold Rle in |- *; right; reflexivity.
  apply (Rle_trans (Rabs (x ^ m)) (Rabs (x ^ n)) (Rabs (x ^ S n))).
  apply Hrecn; assumption.
  simpl in |- *; rewrite Rabs_mult.
  pattern (Rabs (x ^ n)) at 1 in |- *.
  rewrite <- Rmult_1_r.
  rewrite (Rmult_comm (Rabs x) (Rabs (x ^ n))).
  apply Rmult_le_compat_l.
  apply Rabs_pos.
  unfold Rgt in H.
  apply Rlt_le; assumption.
Qed.

Lemma RPow_abs : forall (x:R) (n:nat), Rabs x ^ n = Rabs (x ^ n).
Proof.
  intro; simple induction n; simpl in |- *.
  apply sym_eq; apply Rabs_pos_eq; apply Rlt_le; apply Rlt_0_1.
  intros; rewrite H; apply sym_eq; apply Rabs_mult.
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
  apply Rle_ge; apply poly; fold (Rabs x - 1 > 0) in |- *; apply Rgt_minus;
    assumption.
  apply (Rge_trans (1 + INR x0 * (Rabs x - 1)) (INR x0 * (Rabs x - 1)) b).
  apply Rle_ge; apply Rlt_le; rewrite (Rplus_comm 1 (INR x0 * (Rabs x - 1)));
    pattern (INR x0 * (Rabs x - 1)) at 1 in |- *;
      rewrite <- (let (H1, H2) := Rplus_ne (INR x0 * (Rabs x - 1)) in H1);
        apply Rplus_lt_compat_l; apply Rlt_0_1.
  cut (b = b * / (Rabs x - 1) * (Rabs x - 1)).
  intros; rewrite H4; apply Rmult_ge_compat_r.
  apply Rge_minus; unfold Rge in |- *; left; assumption.
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
  unfold Rge in |- *; left; assumption.
  exists 0%nat;
    apply
      (Rge_trans (INR 0) (IZR (up (b * / (Rabs x - 1)))) (b * / (Rabs x - 1))).
  rewrite INR_IZR_INZ; apply IZR_ge; simpl in |- *; omega.
  unfold Rge in |- *; left; assumption.
  omega.
Qed.

Lemma pow_ne_zero : forall n:nat, n <> 0%nat -> 0 ^ n = 0.
Proof.
  simple induction n.
  simpl in |- *; auto.
  intros; elim H; reflexivity.
  intros; simpl in |- *; apply Rmult_0_l.
Qed.

Lemma Rinv_pow : forall (x:R) (n:nat), x <> 0 -> / x ^ n = (/ x) ^ n.
Proof.
  intros; elim n; simpl in |- *.
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
  pattern (/ y) at 1 in |- *.
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
  right; unfold Rgt in |- *; assumption.
  rewrite <- (Rinv_involutive 1).
  rewrite Rabs_Rinv.
  unfold Rgt in |- *; apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat.
  apply Rabs_pos_lt.
  assumption.
  rewrite Rinv_1; apply Rlt_0_1.
  rewrite Rinv_1; assumption.
  assumption.
  red in |- *; intro; apply R1_neq_R0; assumption.
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
  simpl in |- *; apply Rlt_irrefl; auto.
  rewrite Rabs_Rinv; auto.
  rewrite <- Rinv_pow; auto.
  rewrite RPow_abs; auto.
  rewrite H'0; rewrite Rabs_right; auto with real.
  apply Rle_ge; auto with real.
  apply Rlt_pow; auto with arith.
  rewrite Rabs_Rinv; auto.
  apply Rmult_lt_reg_l with (r := Rabs r).
  case (Rabs_pos r); auto.
  intros H'3; case Eq2; auto.
  rewrite Rmult_1_r; rewrite Rinv_r; auto with real.
  red in |- *; intro; absurd (r ^ S n0 = 1); auto.
  simpl in |- *; rewrite H; rewrite Rmult_0_l; auto with real.
  generalize H'; case n; auto.
  intros n0 H'0.
  cut (r <> 0); [ intros Eq1 | auto with real ].
  cut (Rabs r <> 0); [ intros Eq2 | apply Rabs_no_R0 ]; auto.
  absurd (Rabs r ^ 0 < Rabs r ^ S n0); auto with real arith.
  repeat rewrite RPow_abs; rewrite H'0; simpl in |- *; auto with real.
  red in |- *; intro; absurd (r ^ S n0 = 1); auto.
  simpl in |- *; rewrite H; rewrite Rmult_0_l; auto with real.
Qed.

Lemma pow_Rsqr : forall (x:R) (n:nat), x ^ (2 * n) = Rsqr x ^ n.
Proof.
  intros; induction  n as [| n Hrecn].
  reflexivity.
  replace (2 * S n)%nat with (S (S (2 * n))).
  replace (x ^ S (S (2 * n))) with (x * x * x ^ (2 * n)).
  rewrite Hrecn; reflexivity.
  simpl in |- *; ring.
  ring.
Qed.

Lemma pow_le : forall (a:R) (n:nat), 0 <= a -> 0 <= a ^ n.
Proof.
  intros; induction  n as [| n Hrecn].
  simpl in |- *; left; apply Rlt_0_1.
  simpl in |- *; apply Rmult_le_pos; assumption.
Qed.

(**********)
Lemma pow_1_even : forall n:nat, (-1) ^ (2 * n) = 1.
Proof.
  intro; induction  n as [| n Hrecn].
  reflexivity.
  replace (2 * S n)%nat with (2 + 2 * n)%nat by ring.
  rewrite pow_add; rewrite Hrecn; simpl in |- *; ring.
Qed.

(**********)
Lemma pow_1_odd : forall n:nat, (-1) ^ S (2 * n) = -1.
Proof.
  intro; replace (S (2 * n)) with (2 * n + 1)%nat by ring.
  rewrite pow_add; rewrite pow_1_even; simpl in |- *; ring.
Qed.

(**********)
Lemma pow_1_abs : forall n:nat, Rabs ((-1) ^ n) = 1.
Proof.
  intro; induction  n as [| n Hrecn].
  simpl in |- *; apply Rabs_R1.
  replace (S n) with (n + 1)%nat; [ rewrite pow_add | ring ].
  rewrite Rabs_mult.
  rewrite Hrecn; rewrite Rmult_1_l; simpl in |- *; rewrite Rmult_1_r;
    rewrite Rabs_Ropp; apply Rabs_R1.
Qed.

Lemma pow_mult : forall (x:R) (n1 n2:nat), x ^ (n1 * n2) = (x ^ n1) ^ n2.
Proof.
  intros; induction  n2 as [| n2 Hrecn2].
  simpl in |- *; replace (n1 * 0)%nat with 0%nat; [ reflexivity | ring ].
  replace (n1 * S n2)%nat with (n1 * n2 + n1)%nat.
  replace (S n2) with (n2 + 1)%nat by ring.
  do 2 rewrite pow_add.
  rewrite Hrecn2.
  simpl in |- *.
  ring.
  ring.
Qed.

Lemma pow_incr : forall (x y:R) (n:nat), 0 <= x <= y -> x ^ n <= y ^ n.
Proof.
  intros.
  induction  n as [| n Hrecn].
  right; reflexivity.
  simpl in |- *.
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
  simpl in |- *.
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
  pattern (x ^ m) at 1 in |- *; rewrite <- Rmult_1_r.
  apply Rmult_le_compat_l.
  apply pow_le; left; apply Rlt_le_trans with 1; [ apply Rlt_0_1 | assumption ].
  apply pow_R1_Rle; assumption.
  rewrite plus_comm.
  symmetry  in |- *; apply le_plus_minus; assumption.
Qed.

Lemma pow1 : forall n:nat, 1 ^ n = 1.
Proof.
  intro; induction  n as [| n Hrecn].
  reflexivity.
  simpl in |- *; rewrite Hrecn; rewrite Rmult_1_r; reflexivity.
Qed.

Lemma pow_Rabs : forall (x:R) (n:nat), x ^ n <= Rabs x ^ n.
Proof.
  intros; induction  n as [| n Hrecn].
  right; reflexivity.
  simpl in |- *; case (Rcase_abs x); intro.
  apply Rle_trans with (Rabs (x * x ^ n)).
  apply RRle_abs.
  rewrite Rabs_mult.
  apply Rmult_le_compat_l.
  apply Rabs_pos.
  right; symmetry  in |- *; apply RPow_abs.
  pattern (Rabs x) at 1 in |- *; rewrite (Rabs_right x r);
    apply Rmult_le_compat_l.
  apply Rge_le; exact r.
  apply Hrecn.
Qed.

Lemma pow_maj_Rabs : forall (x y:R) (n:nat), Rabs y <= x -> y ^ n <= x ^ n.
Proof.
  intros; cut (0 <= x).
  intro; apply Rle_trans with (Rabs y ^ n).
  apply pow_Rabs.
  induction  n as [| n Hrecn].
  right; reflexivity.
  simpl in |- *; apply Rle_trans with (x * Rabs y ^ n).
  do 2 rewrite <- (Rmult_comm (Rabs y ^ n)).
  apply Rmult_le_compat_l.
  apply pow_le; apply Rabs_pos.
  assumption.
  apply Rmult_le_compat_l.
  apply H0.
  apply Hrecn.
  apply Rle_trans with (Rabs y); [ apply Rabs_pos | exact H ].
Qed.

(*******************************)
(** *       PowerRZ            *)
(*******************************)
(*i Due to L.Thery i*)

Ltac case_eq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.

Definition powerRZ (x:R) (n:Z) :=
  match n with
    | Z0 => 1
    | Zpos p => x ^ nat_of_P p
    | Zneg p => / x ^ nat_of_P p
  end.

Infix Local "^Z" := powerRZ (at level 30, right associativity) : R_scope.

Lemma Zpower_NR0 :
  forall (x:Z) (n:nat), (0 <= x)%Z -> (0 <= Zpower_nat x n)%Z.
Proof.
  induction n; unfold Zpower_nat in |- *; simpl in |- *; auto with zarith.
Qed.

Lemma powerRZ_O : forall x:R, x ^Z 0 = 1.
Proof.
  reflexivity.
Qed.

Lemma powerRZ_1 : forall x:R, x ^Z Zsucc 0 = x.
Proof.
  simpl in |- *; auto with real.
Qed.

Lemma powerRZ_NOR : forall (x:R) (z:Z), x <> 0 -> x ^Z z <> 0.
Proof.
  destruct z; simpl in |- *; auto with real.
Qed.

Lemma powerRZ_add :
  forall (x:R) (n m:Z), x <> 0 -> x ^Z (n + m) = x ^Z n * x ^Z m.
Proof.
  intro x; destruct n as [| n1| n1]; destruct m as [| m1| m1]; simpl in |- *;
    auto with real.
(* POS/POS *)
  rewrite nat_of_P_plus_morphism; auto with real.
(* POS/NEG *)
  case_eq ((n1 ?= m1)%positive Datatypes.Eq); simpl in |- *; auto with real.
  intros H' H'0; rewrite Pcompare_Eq_eq with (1 := H'); auto with real.
  intros H' H'0; rewrite (nat_of_P_minus_morphism m1 n1); auto with real.
  rewrite (pow_RN_plus x (nat_of_P m1 - nat_of_P n1) (nat_of_P n1));
    auto with real.
  rewrite plus_comm; rewrite le_plus_minus_r; auto with real.
  rewrite Rinv_mult_distr; auto with real.
  rewrite Rinv_involutive; auto with real.
  apply lt_le_weak.
  apply nat_of_P_lt_Lt_compare_morphism; auto.
  apply ZC2; auto.
  intros H' H'0; rewrite (nat_of_P_minus_morphism n1 m1); auto with real.
  rewrite (pow_RN_plus x (nat_of_P n1 - nat_of_P m1) (nat_of_P m1));
    auto with real.
  rewrite plus_comm; rewrite le_plus_minus_r; auto with real.
  apply lt_le_weak.
  change (nat_of_P n1 > nat_of_P m1)%nat in |- *.
  apply nat_of_P_gt_Gt_compare_morphism; auto.
(* NEG/POS *)
  case_eq ((n1 ?= m1)%positive Datatypes.Eq); simpl in |- *; auto with real.
  intros H' H'0; rewrite Pcompare_Eq_eq with (1 := H'); auto with real.
  intros H' H'0; rewrite (nat_of_P_minus_morphism m1 n1); auto with real.
  rewrite (pow_RN_plus x (nat_of_P m1 - nat_of_P n1) (nat_of_P n1));
    auto with real.
  rewrite plus_comm; rewrite le_plus_minus_r; auto with real.
  apply lt_le_weak.
  apply nat_of_P_lt_Lt_compare_morphism; auto.
  apply ZC2; auto.
  intros H' H'0; rewrite (nat_of_P_minus_morphism n1 m1); auto with real.
  rewrite (pow_RN_plus x (nat_of_P n1 - nat_of_P m1) (nat_of_P m1));
    auto with real.
  rewrite plus_comm; rewrite le_plus_minus_r; auto with real.
  rewrite Rinv_mult_distr; auto with real.
  apply lt_le_weak.
  change (nat_of_P n1 > nat_of_P m1)%nat in |- *.
  apply nat_of_P_gt_Gt_compare_morphism; auto.
(* NEG/NEG *)
  rewrite nat_of_P_plus_morphism; auto with real.
  intros H'; rewrite pow_add; auto with real.
  apply Rinv_mult_distr; auto.
  apply pow_nonzero; auto.
  apply pow_nonzero; auto.
Qed.
Hint Resolve powerRZ_O powerRZ_1 powerRZ_NOR powerRZ_add: real.

Lemma Zpower_nat_powerRZ :
  forall n m:nat, IZR (Zpower_nat (Z_of_nat n) m) = INR n ^Z Z_of_nat m.
Proof.
  intros n m; elim m; simpl in |- *; auto with real.
  intros m1 H'; rewrite nat_of_P_o_P_of_succ_nat_eq_succ; simpl in |- *.
  replace (Zpower_nat (Z_of_nat n) (S m1)) with
  (Z_of_nat n * Zpower_nat (Z_of_nat n) m1)%Z.
  rewrite mult_IZR; auto with real.
  repeat rewrite <- INR_IZR_INZ; simpl in |- *.
  rewrite H'; simpl in |- *.
  case m1; simpl in |- *; auto with real.
  intros m2; rewrite nat_of_P_o_P_of_succ_nat_eq_succ; auto.
  unfold Zpower_nat in |- *; auto.
Qed.

Lemma powerRZ_lt : forall (x:R) (z:Z), 0 < x -> 0 < x ^Z z.
Proof.
  intros x z; case z; simpl in |- *; auto with real.
Qed.
Hint Resolve powerRZ_lt: real.

Lemma powerRZ_le : forall (x:R) (z:Z), 0 < x -> 0 <= x ^Z z.
Proof.
  intros x z H'; apply Rlt_le; auto with real.
Qed.
Hint Resolve powerRZ_le: real.

Lemma Zpower_nat_powerRZ_absolu :
  forall n m:Z, (0 <= m)%Z -> IZR (Zpower_nat n (Zabs_nat m)) = IZR n ^Z m.
Proof.
  intros n m; case m; simpl in |- *; auto with zarith.
  intros p H'; elim (nat_of_P p); simpl in |- *; auto with zarith.
  intros n0 H'0; rewrite <- H'0; simpl in |- *; auto with zarith.
  rewrite <- mult_IZR; auto.
  intros p H'; absurd (0 <= Zneg p)%Z; auto with zarith.
Qed.

Lemma powerRZ_R1 : forall n:Z, 1 ^Z n = 1.
Proof.
  intros n; case n; simpl in |- *; auto.
  intros p; elim (nat_of_P p); simpl in |- *; auto; intros n0 H'; rewrite H';
    ring.
  intros p; elim (nat_of_P p); simpl in |- *.
  exact Rinv_1.
  intros n1 H'; rewrite Rinv_mult_distr; try rewrite Rinv_1; try rewrite H';
    auto with real.
Qed.

(*******************************)
(* For easy interface          *)
(*******************************)
(* decimal_exp r z is defined as r 10^z *)

Definition decimal_exp (r:R) (z:Z) : R := (r * 10 ^Z z).


(*******************************)
(** * Sum of n first naturals  *)
(*******************************)
(*********)
Boxed Fixpoint sum_nat_f_O (f:nat -> nat) (n:nat) {struct n} : nat :=
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
Fixpoint sum_f_R0 (f:nat -> R) (N:nat) {struct N} : R :=
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
  intros; induction  n as [| n Hrecn]; simpl in |- *.
  ring.
  rewrite Rmult_plus_distr_r; rewrite Hrecn; cut ((n + 1)%nat = S n).
  intro H; rewrite H; simpl in |- *; ring.
  omega.
Qed.

Lemma sum_f_R0_triangle :
  forall (x:nat -> R) (n:nat),
    Rabs (sum_f_R0 x n) <= sum_f_R0 (fun i:nat => Rabs (x i)) n.
Proof.
  intro; simple induction n; simpl in |- *.
  unfold Rle in |- *; right; reflexivity.
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
  intros; unfold R_dist in |- *; unfold Rabs in |- *; case (Rcase_abs (x - y));
    intro l.
  unfold Rge in |- *; left; apply (Ropp_gt_lt_0_contravar (x - y) l).
  trivial.
Qed.

(*********)
Lemma R_dist_sym : forall x y:R, R_dist x y = R_dist y x.
Proof.
  unfold R_dist in |- *; intros; split_Rabs; try ring.
  generalize (Ropp_gt_lt_0_contravar (y - x) r); intro;
    rewrite (Ropp_minus_distr y x) in H; generalize (Rlt_asym (x - y) 0 r0);
      intro; unfold Rgt in H; elimtype False; auto.
  generalize (minus_Rge y x r); intro; generalize (minus_Rge x y r0); intro;
    generalize (Rge_antisym x y H0 H); intro; rewrite H1; 
      ring.
Qed.

(*********)
Lemma R_dist_refl : forall x y:R, R_dist x y = 0 <-> x = y.
Proof.
  unfold R_dist in |- *; intros; split_Rabs; split; intros.
  rewrite (Ropp_minus_distr x y) in H; apply sym_eq;
    apply (Rminus_diag_uniq y x H).
  rewrite (Ropp_minus_distr x y); generalize (sym_eq H); intro;
    apply (Rminus_diag_eq y x H0).
  apply (Rminus_diag_uniq x y H).
  apply (Rminus_diag_eq x y H). 
Qed.

Lemma R_dist_eq : forall x:R, R_dist x x = 0.
Proof.
  unfold R_dist in |- *; intros; split_Rabs; intros; ring.
Qed.

(***********)
Lemma R_dist_tri : forall x y z:R, R_dist x y <= R_dist x z + R_dist z y.
Proof.
  intros; unfold R_dist in |- *; replace (x - y) with (x - z + (z - y));
    [ apply (Rabs_triang (x - z) (z - y)) | ring ].
Qed.

(*********)
Lemma R_dist_plus :
  forall a b c d:R, R_dist (a + c) (b + d) <= R_dist a b + R_dist c d.
Proof.
  intros; unfold R_dist in |- *;
    replace (a + c - (b + d)) with (a - b + (c - d)).
  exact (Rabs_triang (a - b) (c - d)).
  ring.
Qed.

(*******************************)
(** *     Infinit Sum          *)
(*******************************)
(*********)
Definition infinit_sum (s:nat -> R) (l:R) : Prop :=
  forall eps:R,
    eps > 0 ->
    exists N : nat,
      (forall n:nat, (n >= N)%nat -> R_dist (sum_f_R0 s n) l < eps).
