Require Import NZAxioms.
Require Import NZBase.

Module NZPlusPropFunct (Import NZAxiomsMod : NZAxiomsSig).
Module Export NZBasePropMod := NZBasePropFunct NZAxiomsMod.
Open Local Scope NatIntScope.

Theorem NZplus_0_r : forall n : NZ, n + 0 == n.
Proof.
NZinduct n. now rewrite NZplus_0_l.
intro. rewrite NZplus_succ_l. now rewrite NZsucc_inj_wd.
Qed.

Theorem NZplus_succ_r : forall n m : NZ, n + S m == S (n + m).
Proof.
intros n m; NZinduct n.
now do 2 rewrite NZplus_0_l.
intro. repeat rewrite NZplus_succ_l. now rewrite NZsucc_inj_wd.
Qed.

Theorem NZplus_comm : forall n m : NZ, n + m == m + n.
Proof.
intros n m; NZinduct n.
rewrite NZplus_0_l; now rewrite NZplus_0_r.
intros n. rewrite NZplus_succ_l; rewrite NZplus_succ_r. now rewrite NZsucc_inj_wd.
Qed.

Theorem NZplus_1_l : forall n : NZ, 1 + n == S n.
Proof.
intro n; rewrite NZplus_succ_l; now rewrite NZplus_0_l.
Qed.

Theorem NZplus_1_r : forall n : NZ, n + 1 == S n.
Proof.
intro n; rewrite NZplus_comm; apply NZplus_1_l.
Qed.

Theorem NZplus_assoc : forall n m p : NZ, n + (m + p) == (n + m) + p.
Proof.
intros n m p; NZinduct n.
now do 2 rewrite NZplus_0_l.
intro. do 3 rewrite NZplus_succ_l. now rewrite NZsucc_inj_wd.
Qed.

Theorem NZplus_shuffle1 : forall n m p q : NZ, (n + m) + (p + q) == (n + p) + (m + q).
Proof.
intros n m p q.
rewrite <- (NZplus_assoc n m (p + q)). rewrite (NZplus_comm m (p + q)).
rewrite <- (NZplus_assoc p q m). rewrite (NZplus_assoc n p (q + m)).
now rewrite (NZplus_comm q m).
Qed.

Theorem NZplus_shuffle2 : forall n m p q : NZ, (n + m) + (p + q) == (n + q) + (m + p).
Proof.
intros n m p q.
rewrite <- (NZplus_assoc n m (p + q)). rewrite (NZplus_assoc m p q).
rewrite (NZplus_comm (m + p) q). now rewrite <- (NZplus_assoc n q (m + p)).
Qed.

Theorem NZplus_cancel_l : forall n m p : NZ, p + n == p + m <-> n == m.
Proof.
intros n m p; NZinduct p.
now do 2 rewrite NZplus_0_l.
intro p. do 2 rewrite NZplus_succ_l. now rewrite NZsucc_inj_wd.
Qed.

Theorem NZplus_cancel_r : forall n m p : NZ, n + p == m + p <-> n == m.
Proof.
intros n m p. rewrite (NZplus_comm n p); rewrite (NZplus_comm m p).
apply NZplus_cancel_l.
Qed.

Theorem NZminus_1_r : forall n : NZ, n - 1 == P n.
Proof.
intro n; rewrite NZminus_succ_r; now rewrite NZminus_0_r.
Qed.

End NZPlusPropFunct.

