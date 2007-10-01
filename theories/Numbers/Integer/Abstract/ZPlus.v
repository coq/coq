Require Export ZBase.

Module ZPlusPropFunct (Import ZAxiomsMod : ZAxiomsSig).
Module Export ZBasePropMod := ZBasePropFunct ZAxiomsMod.
Open Local Scope NatIntScope.

Theorem Zplus_0_l : forall n : Z, 0 + n == n.
Proof NZplus_0_l.

Theorem Zplus_succ_l : forall n m : Z, (S n) + m == S (n + m).
Proof NZplus_succ_l.

Theorem Zminus_0_r : forall n : Z, n - 0 == n.
Proof NZminus_0_r.

Theorem Zminus_succ_r : forall n m : Z, n - (S m) == P (n - m).
Proof NZminus_succ_r.

Theorem Zopp_0 : - 0 == 0.
Proof Zopp_0.

Theorem Zopp_succ : forall n : Z, - (S n) == P (- n).
Proof Zopp_succ.

(** Theorems that are valid for both natural numbers and integers *)

Theorem Zplus_0_r : forall n : Z, n + 0 == n.
Proof NZplus_0_r.

Theorem Zplus_succ_r : forall n m : Z, n + S m == S (n + m).
Proof NZplus_succ_r.

Theorem Zplus_comm : forall n m : Z, n + m == m + n.
Proof NZplus_comm.

Theorem Zplus_assoc : forall n m p : Z, n + (m + p) == (n + m) + p.
Proof NZplus_assoc.

Theorem Zplus_shuffle1 : forall n m p q : Z, (n + m) + (p + q) == (n + p) + (m + q).
Proof NZplus_shuffle1.

Theorem Zplus_shuffle2 : forall n m p q : Z, (n + m) + (p + q) == (n + q) + (m + p).
Proof NZplus_shuffle2.

Theorem Zplus_1_l : forall n : Z, 1 + n == S n.
Proof NZplus_1_l.

Theorem Zplus_1_r : forall n : Z, n + 1 == S n.
Proof NZplus_1_r.

Theorem Zplus_cancel_l : forall n m p : Z, p + n == p + m <-> n == m.
Proof NZplus_cancel_l.

Theorem Zplus_cancel_r : forall n m p : Z, n + p == m + p <-> n == m.
Proof NZplus_cancel_r.

(** Theorems that are either not valid on N or have different proofs on N and Z *)

Theorem Zplus_pred_l : forall n m : Z, P n + m == P (n + m).
Proof.
intros n m.
pattern n at 2. qsetoid_rewrite <- (Zsucc_pred n).
rewrite Zplus_succ_l. now rewrite Zpred_succ.
Qed.

Theorem Zplus_pred_r : forall n m : Z, n + P m == P (n + m).
Proof.
intros n m; rewrite (Zplus_comm n (P m)), (Zplus_comm n m);
apply Zplus_pred_l.
Qed.

Theorem Zplus_opp_minus : forall n m : Z, n + (- m) == n - m.
Proof.
NZinduct m.
rewrite Zopp_0; rewrite Zminus_0_r; now rewrite Zplus_0_r.
intro m. rewrite Zopp_succ, Zminus_succ_r, Zplus_pred_r; now rewrite Zpred_inj_wd.
Qed.

Theorem Zminus_0_l : forall n : Z, 0 - n == - n.
Proof.
intro n; rewrite <- Zplus_opp_minus; now rewrite Zplus_0_l.
Qed.

Theorem Zminus_succ_l : forall n m : Z, S n - m == S (n - m).
Proof.
intros n m; do 2 rewrite <- Zplus_opp_minus; now rewrite Zplus_succ_l.
Qed.

Theorem Zminus_pred_l : forall n m : Z, P n - m == P (n - m).
Proof.
intros n m. pattern n at 2; qsetoid_rewrite <- (Zsucc_pred n).
rewrite Zminus_succ_l; now rewrite Zpred_succ.
Qed.

Theorem Zminus_pred_r : forall n m : Z, n - (P m) == S (n - m).
Proof.
intros n m. pattern m at 2; qsetoid_rewrite <- (Zsucc_pred m).
rewrite Zminus_succ_r; now rewrite Zsucc_pred.
Qed.

Theorem Zopp_pred : forall n : Z, - (P n) == S (- n).
Proof.
intro n. pattern n at 2; qsetoid_rewrite <- (Zsucc_pred n).
rewrite Zopp_succ. now rewrite Zsucc_pred.
Qed.

Theorem Zminus_diag : forall n : Z, n - n == 0.
Proof.
NZinduct n.
now rewrite Zminus_0_r.
intro n. rewrite Zminus_succ_r, Zminus_succ_l; now rewrite Zpred_succ.
Qed.

Theorem Zplus_opp_r : forall n : Z, n + (- n) == 0.
Proof.
intro n; rewrite Zplus_opp_minus; now rewrite Zminus_diag.
Qed.

Theorem Zplus_opp_l : forall n : Z, - n + n == 0.
Proof.
intro n; rewrite Zplus_comm; apply Zplus_opp_r.
Qed.

Theorem Zminus_swap : forall n m : Z, - m + n == n - m.
Proof.
intros n m; rewrite <- Zplus_opp_minus; now rewrite Zplus_comm.
Qed.

Theorem Zplus_minus_assoc : forall n m p : Z, n + (m - p) == (n + m) - p.
Proof.
intros n m p; do 2 rewrite <- Zplus_opp_minus; now rewrite Zplus_assoc.
Qed.

Theorem Zopp_involutive : forall n : Z, - (- n) == n.
Proof.
NZinduct n.
now do 2 rewrite Zopp_0.
intro n. rewrite Zopp_succ, Zopp_pred; now rewrite Zsucc_inj_wd.
Qed.

Theorem Zopp_plus_distr : forall n m : Z, - (n + m) == - n + (- m).
Proof.
intros n m; NZinduct n.
rewrite Zopp_0; now do 2 rewrite Zplus_0_l.
intro n. rewrite Zplus_succ_l; do 2 rewrite Zopp_succ; rewrite Zplus_pred_l.
now rewrite Zpred_inj_wd.
Qed.

Theorem Zopp_minus_distr : forall n m : Z, - (n - m) == - n + m.
Proof.
intros n m; rewrite <- Zplus_opp_minus, Zopp_plus_distr.
now rewrite Zopp_involutive.
Qed.

Theorem Zopp_inj : forall n m : Z, - n == - m -> n == m.
Proof.
intros n m H. apply Zopp_wd in H. now do 2 rewrite Zopp_involutive in H.
Qed.

Theorem Zopp_inj_wd : forall n m : Z, - n == - m <-> n == m.
Proof.
intros n m; split; [apply Zopp_inj | apply Zopp_wd].
Qed.

Theorem Zminus_plus_distr : forall n m p : Z, n - (m + p) == (n - m) - p.
Proof.
intros n m p; rewrite <- Zplus_opp_minus, Zopp_plus_distr, Zplus_assoc.
now do 2 rewrite Zplus_opp_minus.
Qed.

Theorem Zminus_minus_distr : forall n m p : Z, n - (m - p) == (n - m) + p.
Proof.
intros n m p; rewrite <- Zplus_opp_minus, Zopp_minus_distr, Zplus_assoc.
now rewrite Zplus_opp_minus.
Qed.

Theorem Zminus_opp : forall n m : Z, n - (- m) == n + m.
Proof.
intros n m; rewrite <- Zplus_opp_minus; now rewrite Zopp_involutive.
Qed.

Theorem Zplus_minus_swap : forall n m p : Z, n + m - p == n - p + m.
Proof.
intros n m p. rewrite <- Zplus_minus_assoc, <- (Zplus_opp_minus n p), <- Zplus_assoc.
now rewrite Zminus_swap.
Qed.

Theorem Zminus_plus_diag : forall n m : Z, n - m + m == n.
Proof.
intros; rewrite <- Zplus_minus_swap; rewrite <- Zplus_minus_assoc;
rewrite Zminus_diag; now rewrite Zplus_0_r.
Qed.

Theorem Zplus_minus_diag : forall n m : Z, n + m - m == n.
Proof.
intros; rewrite <- Zplus_minus_assoc; rewrite Zminus_diag; now rewrite Zplus_0_r.
Qed.

Theorem Zplus_minus_eq_l : forall n m p : Z, m + p == n <-> n - m == p.
Proof.
intros n m p.
stepl (-m + (m + p) == -m + n) by apply Zplus_cancel_l.
stepr (p == n - m) by now split.
rewrite Zplus_assoc, Zplus_opp_l, Zplus_0_l. now rewrite Zminus_swap.
Qed.

Theorem Zplus_minus_eq_r : forall n m p : Z, m + p == n <-> n - p == m.
Proof.
intros n m p; rewrite Zplus_comm; now apply Zplus_minus_eq_l.
Qed.

Theorem Zminus_eq : forall n m : Z, n - m == 0 <-> n == m.
Proof.
intros n m. rewrite <- Zplus_minus_eq_l, Zplus_0_r; now split.
Qed.

End ZPlusPropFunct.

