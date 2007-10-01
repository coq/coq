Require Export Ring.
Require Export ZPlus.

Module ZTimesPropFunct (Import ZAxiomsMod : ZAxiomsSig).
Module Export ZPlusPropMod := ZPlusPropFunct ZAxiomsMod.
Open Local Scope NatIntScope.

Theorem Ztimes_0_r : forall n : Z, n * 0 == 0.
Proof NZtimes_0_r.

Theorem Ztimes_succ_r : forall n m : Z, n * (S m) == n * m + n.
Proof NZtimes_succ_r.

(** Theorems that are valid for both natural numbers and integers *)

Theorem Ztimes_0_l : forall n : Z, 0 * n == 0.
Proof NZtimes_0_l.

Theorem Ztimes_succ_l : forall n m : Z, (S n) * m == n * m + m.
Proof NZtimes_succ_l.

Theorem Ztimes_comm : forall n m : Z, n * m == m * n.
Proof NZtimes_comm.

Theorem Ztimes_plus_distr_r : forall n m p : Z, (n + m) * p == n * p + m * p.
Proof NZtimes_plus_distr_r.

Theorem Ztimes_plus_distr_l : forall n m p : Z, n * (m + p) == n * m + n * p.
Proof NZtimes_plus_distr_l.

Theorem Ztimes_assoc : forall n m p : Z, n * (m * p) == (n * m) * p.
Proof NZtimes_assoc.

Theorem Ztimes_1_l : forall n : Z, 1 * n == n.
Proof NZtimes_1_l.

Theorem Ztimes_1_r : forall n : Z, n * 1 == n.
Proof NZtimes_1_r.

(* The following two theorems are true in an ordered ring,
but since they don't mention order, we'll put them here *)

Theorem Ztimes_eq_0 : forall n m : Z, n * m == 0 -> n == 0 \/ m == 0.
Proof NZtimes_eq_0.

Theorem Ztimes_neq_0 : forall n m : Z, n ~= 0 /\ m ~= 0 <-> n * m ~= 0.
Proof NZtimes_neq_0.

(** Z forms a ring *)

Lemma Zring : ring_theory 0 1 NZplus NZtimes NZminus Zopp NZE.
Proof.
constructor.
exact Zplus_0_l.
exact Zplus_comm.
exact Zplus_assoc.
exact Ztimes_1_l.
exact Ztimes_comm.
exact Ztimes_assoc.
exact Ztimes_plus_distr_r.
intros; now rewrite Zplus_opp_minus.
exact Zplus_opp_r.
Qed.

Add Ring ZR : Zring.

(** Theorems that are either not valid on N or have different proofs on N and Z *)

Theorem Ztimes_pred_r : forall n m : Z, n * (P m) == n * m - n.
Proof.
intros n m.
pattern m at 2; qsetoid_rewrite <- (Zsucc_pred m).
now rewrite Ztimes_succ_r, <- Zplus_minus_assoc, Zminus_diag, Zplus_0_r.
Qed.

Theorem Ztimes_pred_l : forall n m : Z, (P n) * m == n * m - m.
Proof.
intros n m; rewrite (Ztimes_comm (P n) m), (Ztimes_comm n m). apply Ztimes_pred_r.
Qed.

Theorem Ztimes_opp_r : forall n m : Z, n * (- m) == - (n * m).
Proof.
intros; ring.
Qed.

Theorem Ztimes_opp_l : forall n m : Z, (- n) * m == - (n * m).
Proof.
intros; ring.
Qed.

Theorem Ztimes_opp_opp : forall n m : Z, (- n) * (- m) == n * m.
Proof.
intros; ring.
Qed.

Theorem Ztimes_minus_distr_r : forall n m p : Z, n * (m - p) == n * m - n * p.
Proof.
intros; ring.
Qed.

Theorem Ztimes_minus_distr_l : forall n m p : Z, (n - m) * p == n * p - m * p.
Proof.
intros; ring.
Qed.

End ZTimesPropFunct.


