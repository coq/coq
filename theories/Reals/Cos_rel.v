(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo_def.
Require Import OmegaTactic.
Local Open Scope R_scope.

Definition A1 (x:R) (N:nat) : R :=
  sum_f_R0 (fun k:nat => (-1) ^ k / INR (fact (2 * k)) * x ^ (2 * k)) N.

Definition B1 (x:R) (N:nat) : R :=
  sum_f_R0 (fun k:nat => (-1) ^ k / INR (fact (2 * k + 1)) * x ^ (2 * k + 1))
    N.

Definition C1 (x y:R) (N:nat) : R :=
  sum_f_R0 (fun k:nat => (-1) ^ k / INR (fact (2 * k)) * (x + y) ^ (2 * k)) N.

Definition Reste1 (x y:R) (N:nat) : R :=
  sum_f_R0
    (fun k:nat =>
       sum_f_R0
         (fun l:nat =>
            (-1) ^ S (l + k) / INR (fact (2 * S (l + k))) *
            x ^ (2 * S (l + k)) * ((-1) ^ (N - l) / INR (fact (2 * (N - l)))) *
            y ^ (2 * (N - l))) (pred (N - k))) (pred N).

Definition Reste2 (x y:R) (N:nat) : R :=
  sum_f_R0
    (fun k:nat =>
       sum_f_R0
         (fun l:nat =>
            (-1) ^ S (l + k) / INR (fact (2 * S (l + k) + 1)) *
            x ^ (2 * S (l + k) + 1) *
            ((-1) ^ (N - l) / INR (fact (2 * (N - l) + 1))) *
            y ^ (2 * (N - l) + 1)) (pred (N - k))) (
    pred N).

Definition Reste (x y:R) (N:nat) : R := Reste2 x y N - Reste1 x y (S N).

(* Here is the main result that will be used to prove that (cos (x+y))=(cos x)(cos y)-(sin x)(sin y) *)
Theorem cos_plus_form :
 forall (x y:R) (n:nat),
   (0 < n)%nat ->
   A1 x (S n) * A1 y (S n) - B1 x n * B1 y n + Reste x y n = C1 x y (S n).
Proof.
intros.
unfold A1, B1.
rewrite
 (cauchy_finite (fun k:nat => (-1) ^ k / INR (fact (2 * k)) * x ^ (2 * k))
    (fun k:nat => (-1) ^ k / INR (fact (2 * k)) * y ^ (2 * k)) (
    S n)).
rewrite
 (cauchy_finite
    (fun k:nat => (-1) ^ k / INR (fact (2 * k + 1)) * x ^ (2 * k + 1))
    (fun k:nat => (-1) ^ k / INR (fact (2 * k + 1)) * y ^ (2 * k + 1)) n H)
 .
unfold Reste.
replace
 (sum_f_R0
    (fun k:nat =>
       sum_f_R0
         (fun l:nat =>
            (-1) ^ S (l + k) / INR (fact (2 * S (l + k))) *
            x ^ (2 * S (l + k)) *
            ((-1) ^ (S n - l) / INR (fact (2 * (S n - l))) *
             y ^ (2 * (S n - l)))) (pred (S n - k))) (
    pred (S n))) with (Reste1 x y (S n)).
replace
 (sum_f_R0
    (fun k:nat =>
       sum_f_R0
         (fun l:nat =>
            (-1) ^ S (l + k) / INR (fact (2 * S (l + k) + 1)) *
            x ^ (2 * S (l + k) + 1) *
            ((-1) ^ (n - l) / INR (fact (2 * (n - l) + 1)) *
             y ^ (2 * (n - l) + 1))) (pred (n - k))) (
    pred n)) with (Reste2 x y n).
replace
 (sum_f_R0
    (fun k:nat =>
       sum_f_R0
         (fun p:nat =>
            (-1) ^ p / INR (fact (2 * p)) * x ^ (2 * p) *
            ((-1) ^ (k - p) / INR (fact (2 * (k - p))) * y ^ (2 * (k - p))))
         k) (S n)) with
 (sum_f_R0
    (fun k:nat =>
       (-1) ^ k / INR (fact (2 * k)) *
       sum_f_R0
         (fun l:nat => C (2 * k) (2 * l) * x ^ (2 * l) * y ^ (2 * (k - l))) k)
    (S n)).
pose
 (sin_nnn :=
  fun n:nat =>
    match n with
    | O => 0
    | S p =>
        (-1) ^ S p / INR (fact (2 * S p)) *
        sum_f_R0
          (fun l:nat =>
             C (2 * S p) (S (2 * l)) * x ^ S (2 * l) * y ^ S (2 * (p - l))) p
    end).
ring_simplify.
unfold Rminus.
replace
(* (-   old ring compat *)
 (-
  sum_f_R0
    (fun k:nat =>
       sum_f_R0
         (fun p:nat =>
            (-1) ^ p / INR (fact (2 * p + 1)) * x ^ (2 * p + 1) *
            ((-1) ^ (k - p) / INR (fact (2 * (k - p) + 1)) *
             y ^ (2 * (k - p) + 1))) k) n) with (sum_f_R0 sin_nnn (S n)).
rewrite <- sum_plus.
unfold C1.
apply sum_eq; intros.
induction  i as [| i Hreci].
simpl.
unfold C; simpl.
field; discrR.
unfold sin_nnn.
rewrite <- Rmult_plus_distr_l.
apply Rmult_eq_compat_l.
rewrite binomial.
pose (Wn := fun i0:nat => C (2 * S i) i0 * x ^ i0 * y ^ (2 * S i - i0)).
replace
 (sum_f_R0
    (fun l:nat => C (2 * S i) (2 * l) * x ^ (2 * l) * y ^ (2 * (S i - l)))
    (S i)) with (sum_f_R0 (fun l:nat => Wn (2 * l)%nat) (S i)).
replace
 (sum_f_R0
    (fun l:nat =>
       C (2 * S i) (S (2 * l)) * x ^ S (2 * l) * y ^ S (2 * (i - l))) i) with
 (sum_f_R0 (fun l:nat => Wn (S (2 * l))) i).
apply sum_decomposition.
apply sum_eq; intros.
unfold Wn.
apply Rmult_eq_compat_l.
replace (2 * S i - S (2 * i0))%nat with (S (2 * (i - i0))).
reflexivity.
omega.
apply sum_eq; intros.
unfold Wn.
apply Rmult_eq_compat_l.
replace (2 * S i - 2 * i0)%nat with (2 * (S i - i0))%nat.
reflexivity.
omega.
replace
 (-
  sum_f_R0
    (fun k:nat =>
       sum_f_R0
         (fun p:nat =>
            (-1) ^ p / INR (fact (2 * p + 1)) * x ^ (2 * p + 1) *
            ((-1) ^ (k - p) / INR (fact (2 * (k - p) + 1)) *
             y ^ (2 * (k - p) + 1))) k) n) with
 (-1 *
  sum_f_R0
    (fun k:nat =>
       sum_f_R0
         (fun p:nat =>
            (-1) ^ p / INR (fact (2 * p + 1)) * x ^ (2 * p + 1) *
            ((-1) ^ (k - p) / INR (fact (2 * (k - p) + 1)) *
             y ^ (2 * (k - p) + 1))) k) n);[idtac|ring].
rewrite scal_sum.
rewrite decomp_sum.
replace (sin_nnn 0%nat) with 0.
rewrite Rplus_0_l.
change (pred (S n)) with n.
   (* replace (pred (S n)) with n; [ idtac | reflexivity ]. *)
apply sum_eq; intros.
rewrite Rmult_comm.
unfold sin_nnn.
rewrite scal_sum.
rewrite scal_sum.
apply sum_eq; intros.
unfold Rdiv.
(*repeat rewrite Rmult_assoc.*)
(* rewrite (Rmult_comm (/ INR (fact (2 * S i)))). *)
repeat rewrite <- Rmult_assoc.
rewrite <- (Rmult_comm (/ INR (fact (2 * S i)))).
repeat rewrite <- Rmult_assoc.
replace (/ INR (fact (2 * S i)) * C (2 * S i) (S (2 * i0))) with
 (/ INR (fact (2 * i0 + 1)) * / INR (fact (2 * (i - i0) + 1))).
replace (S (2 * i0)) with (2 * i0 + 1)%nat; [ idtac | ring ].
replace (S (2 * (i - i0))) with (2 * (i - i0) + 1)%nat; [ idtac | ring ].
replace ((-1) ^ S i) with (-1 * (-1) ^ i0 * (-1) ^ (i - i0)).
ring.
simpl.
pattern i at 2; replace i with (i0 + (i - i0))%nat.
rewrite pow_add.
ring.
symmetry ; apply le_plus_minus; assumption.
unfold C.
unfold Rdiv; repeat rewrite <- Rmult_assoc.
rewrite <- Rinv_l_sym.
rewrite Rmult_1_l.
rewrite Rinv_mult_distr.
replace (S (2 * i0)) with (2 * i0 + 1)%nat;
 [ apply Rmult_eq_compat_l | ring ].
replace (2 * S i - (2 * i0 + 1))%nat with (2 * (i - i0) + 1)%nat.
reflexivity.
omega.
apply INR_fact_neq_0.
apply INR_fact_neq_0.
apply INR_fact_neq_0.
reflexivity.
apply lt_O_Sn.
(* ring. *)
apply sum_eq; intros.
rewrite scal_sum.
apply sum_eq; intros.
unfold Rdiv.
repeat rewrite <- Rmult_assoc.
rewrite <- (Rmult_comm (/ INR (fact (2 * i)))).
repeat rewrite <- Rmult_assoc.
replace (/ INR (fact (2 * i)) * C (2 * i) (2 * i0)) with
 (/ INR (fact (2 * i0)) * / INR (fact (2 * (i - i0)))).
replace ((-1) ^ i) with ((-1) ^ i0 * (-1) ^ (i - i0)).
ring.
pattern i at 2; replace i with (i0 + (i - i0))%nat.
rewrite pow_add.
ring.
symmetry ; apply le_plus_minus; assumption.
unfold C.
unfold Rdiv; repeat rewrite <- Rmult_assoc.
rewrite <- Rinv_l_sym.
rewrite Rmult_1_l.
rewrite Rinv_mult_distr.
replace (2 * i - 2 * i0)%nat with (2 * (i - i0))%nat.
reflexivity.
omega.
apply INR_fact_neq_0.
apply INR_fact_neq_0.
apply INR_fact_neq_0.
unfold Reste2; apply sum_eq; intros.
apply sum_eq; intros.
unfold Rdiv; ring.
unfold Reste1; apply sum_eq; intros.
apply sum_eq; intros.
unfold Rdiv; ring.
apply lt_O_Sn.
Qed.

Lemma pow_sqr : forall (x:R) (i:nat), x ^ (2 * i) = (x * x) ^ i.
Proof.
intros.
assert (H := pow_Rsqr x i).
unfold Rsqr in H; exact H.
Qed.

Lemma A1_cvg : forall x:R, Un_cv (A1 x) (cos x).
Proof.
intro.
unfold cos; destruct (exist_cos (Rsqr x)) as (x0,p).
unfold cos_in, cos_n, infinite_sum, R_dist in p.
unfold Un_cv, R_dist; intros.
destruct (p eps H) as (x1,H0).
exists x1; intros.
unfold A1.
replace
 (sum_f_R0 (fun k:nat => (-1) ^ k / INR (fact (2 * k)) * x ^ (2 * k)) n) with
 (sum_f_R0 (fun i:nat => (-1) ^ i / INR (fact (2 * i)) * (x * x) ^ i) n).
apply H0; assumption.
apply sum_eq.
intros.
replace ((x * x) ^ i) with (x ^ (2 * i)).
reflexivity.
apply pow_sqr.
Qed.

Lemma C1_cvg : forall x y:R, Un_cv (C1 x y) (cos (x + y)).
Proof.
intros.
unfold cos.
destruct (exist_cos (Rsqr (x + y))) as (x0,p).
unfold cos_in, cos_n, infinite_sum, R_dist in p.
unfold Un_cv, R_dist; intros.
destruct (p eps H) as (x1,H0).
exists x1; intros.
unfold C1.
replace
 (sum_f_R0 (fun k:nat => (-1) ^ k / INR (fact (2 * k)) * (x + y) ^ (2 * k)) n)
 with
 (sum_f_R0
    (fun i:nat => (-1) ^ i / INR (fact (2 * i)) * ((x + y) * (x + y)) ^ i) n).
apply H0; assumption.
apply sum_eq.
intros.
replace (((x + y) * (x + y)) ^ i) with ((x + y) ^ (2 * i)).
reflexivity.
apply pow_sqr.
Qed.

Lemma B1_cvg : forall x:R, Un_cv (B1 x) (sin x).
Proof.
intro.
case (Req_dec x 0); intro.
rewrite H.
rewrite sin_0.
unfold B1.
unfold Un_cv; unfold R_dist; intros; exists 0%nat; intros.
replace
 (sum_f_R0 (fun k:nat => (-1) ^ k / INR (fact (2 * k + 1)) * 0 ^ (2 * k + 1))
    n) with 0.
unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0; assumption.
induction  n as [| n Hrecn].
simpl; ring.
rewrite tech5; rewrite <- Hrecn.
simpl; ring.
unfold ge; apply le_O_n.
unfold sin. destruct (exist_sin (Rsqr x)) as (x0,p).
unfold sin_in, sin_n, infinite_sum, R_dist in p.
unfold Un_cv, R_dist; intros.
cut (0 < eps / Rabs x);
 [ intro
 | unfold Rdiv; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; apply Rabs_pos_lt; assumption ] ].
destruct (p (eps / Rabs x) H1) as (x1,H2).
exists x1; intros.
unfold B1.
replace
 (sum_f_R0 (fun k:nat => (-1) ^ k / INR (fact (2 * k + 1)) * x ^ (2 * k + 1))
    n) with
 (x *
  sum_f_R0 (fun i:nat => (-1) ^ i / INR (fact (2 * i + 1)) * (x * x) ^ i) n).
replace
 (x *
  sum_f_R0 (fun i:nat => (-1) ^ i / INR (fact (2 * i + 1)) * (x * x) ^ i) n -
  x * x0) with
 (x *
  (sum_f_R0 (fun i:nat => (-1) ^ i / INR (fact (2 * i + 1)) * (x * x) ^ i) n -
   x0)); [ idtac | ring ].
rewrite Rabs_mult.
apply Rmult_lt_reg_l with (/ Rabs x).
apply Rinv_0_lt_compat; apply Rabs_pos_lt; assumption.
rewrite <- Rmult_assoc, <- Rinv_l_sym, Rmult_1_l, <- (Rmult_comm eps). apply H2;
 assumption.
apply Rabs_no_R0; assumption.
rewrite scal_sum.
apply sum_eq.
intros.
rewrite pow_add.
rewrite pow_sqr.
simpl.
ring.
Qed.
