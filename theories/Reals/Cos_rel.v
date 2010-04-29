(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo_def.
Open Local Scope R_scope.

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
intros.
unfold A1, B1 in |- *.
rewrite
 (cauchy_finite (fun k:nat => (-1) ^ k / INR (fact (2 * k)) * x ^ (2 * k))
    (fun k:nat => (-1) ^ k / INR (fact (2 * k)) * y ^ (2 * k)) (
    S n)).
rewrite
 (cauchy_finite
    (fun k:nat => (-1) ^ k / INR (fact (2 * k + 1)) * x ^ (2 * k + 1))
    (fun k:nat => (-1) ^ k / INR (fact (2 * k + 1)) * y ^ (2 * k + 1)) n H)
 .
unfold Reste in |- *.
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
unfold C1 in |- *.
apply sum_eq; intros.
induction  i as [| i Hreci].
simpl in |- *.
unfold C in |- *; simpl in |- *.
field; discrR.
unfold sin_nnn in |- *.
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
unfold Wn in |- *.
apply Rmult_eq_compat_l.
replace (2 * S i - S (2 * i0))%nat with (S (2 * (i - i0))).
reflexivity.
omega.
apply sum_eq; intros.
unfold Wn in |- *.
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
unfold sin_nnn in |- *.
rewrite scal_sum.
rewrite scal_sum.
apply sum_eq; intros.
unfold Rdiv in |- *.
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
simpl in |- *.
pattern i at 2 in |- *; replace i with (i0 + (i - i0))%nat.
rewrite pow_add.
ring.
symmetry  in |- *; apply le_plus_minus; assumption.
unfold C in |- *.
unfold Rdiv in |- *; repeat rewrite <- Rmult_assoc.
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
unfold Rdiv in |- *.
repeat rewrite <- Rmult_assoc.
rewrite <- (Rmult_comm (/ INR (fact (2 * i)))).
repeat rewrite <- Rmult_assoc.
replace (/ INR (fact (2 * i)) * C (2 * i) (2 * i0)) with
 (/ INR (fact (2 * i0)) * / INR (fact (2 * (i - i0)))).
replace ((-1) ^ i) with ((-1) ^ i0 * (-1) ^ (i - i0)).
ring.
pattern i at 2 in |- *; replace i with (i0 + (i - i0))%nat.
rewrite pow_add.
ring.
symmetry  in |- *; apply le_plus_minus; assumption.
unfold C in |- *.
unfold Rdiv in |- *; repeat rewrite <- Rmult_assoc.
rewrite <- Rinv_l_sym.
rewrite Rmult_1_l.
rewrite Rinv_mult_distr.
replace (2 * i - 2 * i0)%nat with (2 * (i - i0))%nat.
reflexivity.
omega.
apply INR_fact_neq_0.
apply INR_fact_neq_0.
apply INR_fact_neq_0.
unfold Reste2 in |- *; apply sum_eq; intros.
apply sum_eq; intros.
unfold Rdiv in |- *; ring.
unfold Reste1 in |- *; apply sum_eq; intros.
apply sum_eq; intros.
unfold Rdiv in |- *; ring.
apply lt_O_Sn.
Qed.

Lemma pow_sqr : forall (x:R) (i:nat), x ^ (2 * i) = (x * x) ^ i.
intros.
assert (H := pow_Rsqr x i).
unfold Rsqr in H; exact H.
Qed.

Lemma A1_cvg : forall x:R, Un_cv (A1 x) (cos x).
intro.
assert (H := exist_cos (x * x)).
elim H; intros.
assert (p_i := p).
unfold cos_in in p.
unfold cos_n, infinite_sum in p.
unfold R_dist in p.
cut (cos x = x0).
intro.
rewrite H0.
unfold Un_cv in |- *; unfold R_dist in |- *; intros.
elim (p eps H1); intros.
exists x1; intros.
unfold A1 in |- *.
replace
 (sum_f_R0 (fun k:nat => (-1) ^ k / INR (fact (2 * k)) * x ^ (2 * k)) n) with
 (sum_f_R0 (fun i:nat => (-1) ^ i / INR (fact (2 * i)) * (x * x) ^ i) n).
apply H2; assumption.
apply sum_eq.
intros.
replace ((x * x) ^ i) with (x ^ (2 * i)).
reflexivity.
apply pow_sqr.
unfold cos in |- *.
case (exist_cos (Rsqr x)).
unfold Rsqr in |- *; intros.
unfold cos_in in p_i.
unfold cos_in in c.
apply uniqueness_sum with (fun i:nat => cos_n i * (x * x) ^ i); assumption.
Qed.

Lemma C1_cvg : forall x y:R, Un_cv (C1 x y) (cos (x + y)).
intros.
assert (H := exist_cos ((x + y) * (x + y))).
elim H; intros.
assert (p_i := p).
unfold cos_in in p.
unfold cos_n, infinite_sum in p.
unfold R_dist in p.
cut (cos (x + y) = x0).
intro.
rewrite H0.
unfold Un_cv in |- *; unfold R_dist in |- *; intros.
elim (p eps H1); intros.
exists x1; intros.
unfold C1 in |- *.
replace
 (sum_f_R0 (fun k:nat => (-1) ^ k / INR (fact (2 * k)) * (x + y) ^ (2 * k)) n)
 with
 (sum_f_R0
    (fun i:nat => (-1) ^ i / INR (fact (2 * i)) * ((x + y) * (x + y)) ^ i) n).
apply H2; assumption.
apply sum_eq.
intros.
replace (((x + y) * (x + y)) ^ i) with ((x + y) ^ (2 * i)).
reflexivity.
apply pow_sqr.
unfold cos in |- *.
case (exist_cos (Rsqr (x + y))).
unfold Rsqr in |- *; intros.
unfold cos_in in p_i.
unfold cos_in in c.
apply uniqueness_sum with (fun i:nat => cos_n i * ((x + y) * (x + y)) ^ i);
 assumption.
Qed.

Lemma B1_cvg : forall x:R, Un_cv (B1 x) (sin x).
intro.
case (Req_dec x 0); intro.
rewrite H.
rewrite sin_0.
unfold B1 in |- *.
unfold Un_cv in |- *; unfold R_dist in |- *; intros; exists 0%nat; intros.
replace
 (sum_f_R0 (fun k:nat => (-1) ^ k / INR (fact (2 * k + 1)) * 0 ^ (2 * k + 1))
    n) with 0.
unfold Rminus in |- *; rewrite Rplus_opp_r; rewrite Rabs_R0; assumption.
induction  n as [| n Hrecn].
simpl in |- *; ring.
rewrite tech5; rewrite <- Hrecn.
simpl in |- *; ring.
unfold ge in |- *; apply le_O_n.
assert (H0 := exist_sin (x * x)).
elim H0; intros.
assert (p_i := p).
unfold sin_in in p.
unfold sin_n, infinite_sum in p.
unfold R_dist in p.
cut (sin x = x * x0).
intro.
rewrite H1.
unfold Un_cv in |- *; unfold R_dist in |- *; intros.
cut (0 < eps / Rabs x);
 [ intro
 | unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; apply Rabs_pos_lt; assumption ] ].
elim (p (eps / Rabs x) H3); intros.
exists x1; intros.
unfold B1 in |- *.
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
rewrite <- Rmult_assoc.
rewrite <- Rinv_l_sym.
rewrite Rmult_1_l; rewrite <- (Rmult_comm eps); unfold Rdiv in H4; apply H4;
 assumption.
apply Rabs_no_R0; assumption.
rewrite scal_sum.
apply sum_eq.
intros.
rewrite pow_add.
rewrite pow_sqr.
simpl in |- *.
ring.
unfold sin in |- *.
case (exist_sin (Rsqr x)).
unfold Rsqr in |- *; intros.
unfold sin_in in p_i.
unfold sin_in in s.
assert
 (H1 := uniqueness_sum (fun i:nat => sin_n i * (x * x) ^ i) x0 x1 p_i s).
rewrite H1; reflexivity.
Qed.
