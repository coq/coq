(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i $Id$ i*)

Require Import NZAxioms.
Require Import NZBase.

Module NZPlusPropFunct (Import NZAxiomsMod : NZAxiomsSig).
Module Export NZBasePropMod := NZBasePropFunct NZAxiomsMod.
Open Local Scope NatIntScope.

Theorem NZadd_0_r : forall n : NZ, n + 0 == n.
Proof.
NZinduct n. now rewrite NZadd_0_l.
intro. rewrite NZadd_succ_l. now rewrite NZsucc_inj_wd.
Qed.

Theorem NZadd_succ_r : forall n m : NZ, n + S m == S (n + m).
Proof.
intros n m; NZinduct n.
now do 2 rewrite NZadd_0_l.
intro. repeat rewrite NZadd_succ_l. now rewrite NZsucc_inj_wd.
Qed.

Theorem NZadd_comm : forall n m : NZ, n + m == m + n.
Proof.
intros n m; NZinduct n.
rewrite NZadd_0_l; now rewrite NZadd_0_r.
intros n. rewrite NZadd_succ_l; rewrite NZadd_succ_r. now rewrite NZsucc_inj_wd.
Qed.

Theorem NZadd_1_l : forall n : NZ, 1 + n == S n.
Proof.
intro n; rewrite NZadd_succ_l; now rewrite NZadd_0_l.
Qed.

Theorem NZadd_1_r : forall n : NZ, n + 1 == S n.
Proof.
intro n; rewrite NZadd_comm; apply NZadd_1_l.
Qed.

Theorem NZadd_assoc : forall n m p : NZ, n + (m + p) == (n + m) + p.
Proof.
intros n m p; NZinduct n.
now do 2 rewrite NZadd_0_l.
intro. do 3 rewrite NZadd_succ_l. now rewrite NZsucc_inj_wd.
Qed.

Theorem NZadd_shuffle1 : forall n m p q : NZ, (n + m) + (p + q) == (n + p) + (m + q).
Proof.
intros n m p q.
rewrite <- (NZadd_assoc n m (p + q)). rewrite (NZadd_comm m (p + q)).
rewrite <- (NZadd_assoc p q m). rewrite (NZadd_assoc n p (q + m)).
now rewrite (NZadd_comm q m).
Qed.

Theorem NZadd_shuffle2 : forall n m p q : NZ, (n + m) + (p + q) == (n + q) + (m + p).
Proof.
intros n m p q.
rewrite <- (NZadd_assoc n m (p + q)). rewrite (NZadd_assoc m p q).
rewrite (NZadd_comm (m + p) q). now rewrite <- (NZadd_assoc n q (m + p)).
Qed.

Theorem NZadd_cancel_l : forall n m p : NZ, p + n == p + m <-> n == m.
Proof.
intros n m p; NZinduct p.
now do 2 rewrite NZadd_0_l.
intro p. do 2 rewrite NZadd_succ_l. now rewrite NZsucc_inj_wd.
Qed.

Theorem NZadd_cancel_r : forall n m p : NZ, n + p == m + p <-> n == m.
Proof.
intros n m p. rewrite (NZadd_comm n p); rewrite (NZadd_comm m p).
apply NZadd_cancel_l.
Qed.

Theorem NZminus_1_r : forall n : NZ, n - 1 == P n.
Proof.
intro n; rewrite NZminus_succ_r; now rewrite NZminus_0_r.
Qed.

End NZPlusPropFunct.

