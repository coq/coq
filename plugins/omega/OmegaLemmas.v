(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Import ZArith_base.
Open Local Scope Z_scope.

(** Factorization lemmas *)

Theorem Zred_factor0 : forall n:Z, n = n * 1.
  intro x; rewrite (Zmult_1_r x); reflexivity.
Qed.

Theorem Zred_factor1 : forall n:Z, n + n = n * 2.
Proof.
  exact Zplus_diag_eq_mult_2.
Qed.

Theorem Zred_factor2 : forall n m:Z, n + n * m = n * (1 + m).
Proof.
  intros x y; pattern x at 1 in |- *; rewrite <- (Zmult_1_r x);
    rewrite <- Zmult_plus_distr_r; trivial with arith.
Qed.

Theorem Zred_factor3 : forall n m:Z, n * m + n = n * (1 + m).
Proof.
  intros x y; pattern x at 2 in |- *; rewrite <- (Zmult_1_r x);
    rewrite <- Zmult_plus_distr_r; rewrite Zplus_comm; 
      trivial with arith.
Qed.

Theorem Zred_factor4 : forall n m p:Z, n * m + n * p = n * (m + p).
Proof.
  intros x y z; symmetry  in |- *; apply Zmult_plus_distr_r.
Qed.

Theorem Zred_factor5 : forall n m:Z, n * 0 + m = m.
Proof.
  intros x y; rewrite <- Zmult_0_r_reverse; auto with arith.
Qed.

Theorem Zred_factor6 : forall n:Z, n = n + 0.
Proof.
  intro; rewrite Zplus_0_r; trivial with arith.
Qed.

(** Other specific variants of theorems dedicated for the Omega tactic *)

Lemma new_var : forall x : Z, exists y : Z, x = y.
intros x; exists x; trivial with arith. 
Qed.

Lemma OMEGA1 : forall x y : Z, x = y -> 0 <= x -> 0 <= y.
intros x y H; rewrite H; auto with arith.
Qed.

Lemma OMEGA2 : forall x y : Z, 0 <= x -> 0 <= y -> 0 <= x + y.
exact Zplus_le_0_compat.
Qed. 

Lemma OMEGA3 : forall x y k : Z, k > 0 -> x = y * k -> x = 0 -> y = 0.

intros x y k H1 H2 H3; apply (Zmult_integral_l k);
 [ unfold not in |- *; intros H4; absurd (k > 0);
    [ rewrite H4; unfold Zgt in |- *; simpl in |- *; discriminate
    | assumption ]
 | rewrite <- H2; assumption ].
Qed.

Lemma OMEGA4 : forall x y z : Z, x > 0 -> y > x -> z * y + x <> 0.

unfold not in |- *; intros x y z H1 H2 H3; cut (y > 0);
 [ intros H4; cut (0 <= z * y + x);
    [ intros H5; generalize (Zmult_le_approx y z x H4 H2 H5); intros H6;
       absurd (z * y + x > 0);
       [ rewrite H3; unfold Zgt in |- *; simpl in |- *; discriminate
       | apply Zle_gt_trans with x;
          [ pattern x at 1 in |- *; rewrite <- (Zplus_0_l x);
             apply Zplus_le_compat_r; rewrite Zmult_comm; 
             generalize H4; unfold Zgt in |- *; case y;
             [ simpl in |- *; intros H7; discriminate H7
             | intros p H7; rewrite <- (Zmult_0_r (Zpos p));
                unfold Zle in |- *; rewrite Zcompare_mult_compat; 
                exact H6
             | simpl in |- *; intros p H7; discriminate H7 ]
          | assumption ] ]
    | rewrite H3; unfold Zle in |- *; simpl in |- *; discriminate ]
 | apply Zgt_trans with x; [ assumption | assumption ] ].
Qed.

Lemma OMEGA5 : forall x y z : Z, x = 0 -> y = 0 -> x + y * z = 0.

intros x y z H1 H2; rewrite H1; rewrite H2; simpl in |- *; trivial with arith.
Qed.

Lemma OMEGA6 : forall x y z : Z, 0 <= x -> y = 0 -> 0 <= x + y * z.

intros x y z H1 H2; rewrite H2; simpl in |- *; rewrite Zplus_0_r; assumption.
Qed.

Lemma OMEGA7 :
 forall x y z t : Z, z > 0 -> t > 0 -> 0 <= x -> 0 <= y -> 0 <= x * z + y * t.

intros x y z t H1 H2 H3 H4; rewrite <- (Zplus_0_l 0); apply Zplus_le_compat;
 apply Zmult_gt_0_le_0_compat; assumption.
Qed.

Lemma OMEGA8 : forall x y : Z, 0 <= x -> 0 <= y -> x = - y -> x = 0.

intros x y H1 H2 H3; elim (Zle_lt_or_eq 0 x H1);
 [ intros H4; absurd (0 < x);
    [ change (0 >= x) in |- *; apply Zle_ge; apply Zplus_le_reg_l with y;
       rewrite H3; rewrite Zplus_opp_r; rewrite Zplus_0_r; 
       assumption
    | assumption ]
 | intros H4; rewrite H4; trivial with arith ].
Qed.

Lemma OMEGA9 : forall x y z t : Z, y = 0 -> x = z -> y + (- x + z) * t = 0.

intros x y z t H1 H2; rewrite H2; rewrite Zplus_opp_l; rewrite Zmult_0_l;
 rewrite Zplus_0_r; assumption.
Qed.

Lemma OMEGA10 :
 forall v c1 c2 l1 l2 k1 k2 : Z,
 (v * c1 + l1) * k1 + (v * c2 + l2) * k2 =
 v * (c1 * k1 + c2 * k2) + (l1 * k1 + l2 * k2).

intros; repeat rewrite Zmult_plus_distr_l || rewrite Zmult_plus_distr_r;
 repeat rewrite Zmult_assoc; repeat elim Zplus_assoc;
 rewrite (Zplus_permute (l1 * k1) (v * c2 * k2)); trivial with arith.
Qed.

Lemma OMEGA11 :
 forall v1 c1 l1 l2 k1 : Z,
 (v1 * c1 + l1) * k1 + l2 = v1 * (c1 * k1) + (l1 * k1 + l2).

intros; repeat rewrite Zmult_plus_distr_l || rewrite Zmult_plus_distr_r;
 repeat rewrite Zmult_assoc; repeat elim Zplus_assoc; 
 trivial with arith.
Qed.

Lemma OMEGA12 :
 forall v2 c2 l1 l2 k2 : Z,
 l1 + (v2 * c2 + l2) * k2 = v2 * (c2 * k2) + (l1 + l2 * k2).

intros; repeat rewrite Zmult_plus_distr_l || rewrite Zmult_plus_distr_r;
 repeat rewrite Zmult_assoc; repeat elim Zplus_assoc; 
 rewrite Zplus_permute; trivial with arith.
Qed.

Lemma OMEGA13 :
 forall (v l1 l2 : Z) (x : positive),
 v * Zpos x + l1 + (v * Zneg x + l2) = l1 + l2.

intros; rewrite Zplus_assoc; rewrite (Zplus_comm (v * Zpos x) l1);
 rewrite (Zplus_assoc_reverse l1); rewrite <- Zmult_plus_distr_r;
 rewrite <- Zopp_neg; rewrite (Zplus_comm (- Zneg x) (Zneg x));
 rewrite Zplus_opp_r; rewrite Zmult_0_r; rewrite Zplus_0_r;
 trivial with arith.
Qed.
 
Lemma OMEGA14 :
 forall (v l1 l2 : Z) (x : positive),
 v * Zneg x + l1 + (v * Zpos x + l2) = l1 + l2.

intros; rewrite Zplus_assoc; rewrite (Zplus_comm (v * Zneg x) l1);
 rewrite (Zplus_assoc_reverse l1); rewrite <- Zmult_plus_distr_r;
 rewrite <- Zopp_neg; rewrite Zplus_opp_r; rewrite Zmult_0_r;
 rewrite Zplus_0_r; trivial with arith.
Qed.
Lemma OMEGA15 :
 forall v c1 c2 l1 l2 k2 : Z,
 v * c1 + l1 + (v * c2 + l2) * k2 = v * (c1 + c2 * k2) + (l1 + l2 * k2).

intros; repeat rewrite Zmult_plus_distr_l || rewrite Zmult_plus_distr_r;
 repeat rewrite Zmult_assoc; repeat elim Zplus_assoc;
 rewrite (Zplus_permute l1 (v * c2 * k2)); trivial with arith.
Qed.

Lemma OMEGA16 : forall v c l k : Z, (v * c + l) * k = v * (c * k) + l * k.

intros; repeat rewrite Zmult_plus_distr_l || rewrite Zmult_plus_distr_r;
 repeat rewrite Zmult_assoc; repeat elim Zplus_assoc; 
 trivial with arith.
Qed.

Lemma OMEGA17 : forall x y z : Z, Zne x 0 -> y = 0 -> Zne (x + y * z) 0.

unfold Zne, not in |- *; intros x y z H1 H2 H3; apply H1;
 apply Zplus_reg_l with (y * z); rewrite Zplus_comm; 
 rewrite H3; rewrite H2; auto with arith.
Qed.

Lemma OMEGA18 : forall x y k : Z, x = y * k -> Zne x 0 -> Zne y 0.

unfold Zne, not in |- *; intros x y k H1 H2 H3; apply H2; rewrite H1;
 rewrite H3; auto with arith.
Qed.

Lemma OMEGA19 : forall x : Z, Zne x 0 -> 0 <= x + -1 \/ 0 <= x * -1 + -1.

unfold Zne in |- *; intros x H; elim (Zle_or_lt 0 x);
 [ intros H1; elim Zle_lt_or_eq with (1 := H1);
    [ intros H2; left; change (0 <= Zpred x) in |- *; apply Zsucc_le_reg;
       rewrite <- Zsucc_pred; apply Zlt_le_succ; assumption
    | intros H2; absurd (x = 0); auto with arith ]
 | intros H1; right; rewrite <- Zopp_eq_mult_neg_1; rewrite Zplus_comm;
    apply Zle_left; apply Zsucc_le_reg; simpl in |- *; 
    apply Zlt_le_succ; auto with arith ].
Qed.

Lemma OMEGA20 : forall x y z : Z, Zne x 0 -> y = 0 -> Zne (x + y * z) 0.

unfold Zne, not in |- *; intros x y z H1 H2 H3; apply H1; rewrite H2 in H3;
 simpl in H3; rewrite Zplus_0_r in H3; trivial with arith.
Qed.

Definition fast_Zplus_comm (x y : Z) (P : Z -> Prop)
  (H : P (y + x)) := eq_ind_r P H (Zplus_comm x y).

Definition fast_Zplus_assoc_reverse (n m p : Z) (P : Z -> Prop)
  (H : P (n + (m + p))) := eq_ind_r P H (Zplus_assoc_reverse n m p).

Definition fast_Zplus_assoc (n m p : Z) (P : Z -> Prop) 
  (H : P (n + m + p)) := eq_ind_r P H (Zplus_assoc n m p).

Definition fast_Zplus_permute (n m p : Z) (P : Z -> Prop)
  (H : P (m + (n + p))) := eq_ind_r P H (Zplus_permute n m p).

Definition fast_OMEGA10 (v c1 c2 l1 l2 k1 k2 : Z) (P : Z -> Prop)
  (H : P (v * (c1 * k1 + c2 * k2) + (l1 * k1 + l2 * k2))) :=
  eq_ind_r P H (OMEGA10 v c1 c2 l1 l2 k1 k2).

Definition fast_OMEGA11 (v1 c1 l1 l2 k1 : Z) (P : Z -> Prop)
  (H : P (v1 * (c1 * k1) + (l1 * k1 + l2))) :=
  eq_ind_r P H (OMEGA11 v1 c1 l1 l2 k1).
Definition fast_OMEGA12 (v2 c2 l1 l2 k2 : Z) (P : Z -> Prop)
  (H : P (v2 * (c2 * k2) + (l1 + l2 * k2))) :=
  eq_ind_r P H (OMEGA12 v2 c2 l1 l2 k2).

Definition fast_OMEGA15 (v c1 c2 l1 l2 k2 : Z) (P : Z -> Prop)
  (H : P (v * (c1 + c2 * k2) + (l1 + l2 * k2))) :=
  eq_ind_r P H (OMEGA15 v c1 c2 l1 l2 k2).
Definition fast_OMEGA16 (v c l k : Z) (P : Z -> Prop)
  (H : P (v * (c * k) + l * k)) := eq_ind_r P H (OMEGA16 v c l k).

Definition fast_OMEGA13 (v l1 l2 : Z) (x : positive) (P : Z -> Prop)
  (H : P (l1 + l2)) := eq_ind_r P H (OMEGA13 v l1 l2 x).

Definition fast_OMEGA14 (v l1 l2 : Z) (x : positive) (P : Z -> Prop)
  (H : P (l1 + l2)) := eq_ind_r P H (OMEGA14 v l1 l2 x).
Definition fast_Zred_factor0 (x : Z) (P : Z -> Prop) 
  (H : P (x * 1)) := eq_ind_r P H (Zred_factor0 x).

Definition fast_Zopp_eq_mult_neg_1 (x : Z) (P : Z -> Prop)
  (H : P (x * -1)) := eq_ind_r P H (Zopp_eq_mult_neg_1 x).

Definition fast_Zmult_comm (x y : Z) (P : Z -> Prop)
  (H : P (y * x)) := eq_ind_r P H (Zmult_comm x y).

Definition fast_Zopp_plus_distr (x y : Z) (P : Z -> Prop)
  (H : P (- x + - y)) := eq_ind_r P H (Zopp_plus_distr x y).

Definition fast_Zopp_involutive (x : Z) (P : Z -> Prop) (H : P x) :=
  eq_ind_r P H (Zopp_involutive x).

Definition fast_Zopp_mult_distr_r (x y : Z) (P : Z -> Prop) 
  (H : P (x * - y)) := eq_ind_r P H (Zopp_mult_distr_r x y).

Definition fast_Zmult_plus_distr_l (n m p : Z) (P : Z -> Prop)
  (H : P (n * p + m * p)) := eq_ind_r P H (Zmult_plus_distr_l n m p).
Definition fast_Zmult_opp_comm (x y : Z) (P : Z -> Prop) 
  (H : P (x * - y)) := eq_ind_r P H (Zmult_opp_comm x y).

Definition fast_Zmult_assoc_reverse (n m p : Z) (P : Z -> Prop)
  (H : P (n * (m * p))) := eq_ind_r P H (Zmult_assoc_reverse n m p).

Definition fast_Zred_factor1 (x : Z) (P : Z -> Prop) 
  (H : P (x * 2)) := eq_ind_r P H (Zred_factor1 x).

Definition fast_Zred_factor2 (x y : Z) (P : Z -> Prop)
  (H : P (x * (1 + y))) := eq_ind_r P H (Zred_factor2 x y).

Definition fast_Zred_factor3 (x y : Z) (P : Z -> Prop)
  (H : P (x * (1 + y))) := eq_ind_r P H (Zred_factor3 x y).

Definition fast_Zred_factor4 (x y z : Z) (P : Z -> Prop)
  (H : P (x * (y + z))) := eq_ind_r P H (Zred_factor4 x y z).

Definition fast_Zred_factor5 (x y : Z) (P : Z -> Prop) 
  (H : P y) := eq_ind_r P H (Zred_factor5 x y).

Definition fast_Zred_factor6 (x : Z) (P : Z -> Prop) 
  (H : P (x + 0)) := eq_ind_r P H (Zred_factor6 x).
