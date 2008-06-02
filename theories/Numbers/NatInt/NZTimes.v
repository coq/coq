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
Require Import NZPlus.

Module NZTimesPropFunct (Import NZAxiomsMod : NZAxiomsSig).
Module Export NZPlusPropMod := NZPlusPropFunct NZAxiomsMod.
Open Local Scope NatIntScope.

Theorem NZmul_0_r : forall n : NZ, n * 0 == 0.
Proof.
NZinduct n.
now rewrite NZmul_0_l.
intro. rewrite NZmul_succ_l. now rewrite NZadd_0_r.
Qed.

Theorem NZmul_succ_r : forall n m : NZ, n * (S m) == n * m + n.
Proof.
intros n m; NZinduct n.
do 2 rewrite NZmul_0_l; now rewrite NZadd_0_l.
intro n. do 2 rewrite NZmul_succ_l. do 2 rewrite NZadd_succ_r.
rewrite NZsucc_inj_wd. rewrite <- (NZadd_assoc (n * m) m n).
rewrite (NZadd_comm m n). rewrite NZadd_assoc.
now rewrite NZadd_cancel_r.
Qed.

Theorem NZmul_comm : forall n m : NZ, n * m == m * n.
Proof.
intros n m; NZinduct n.
rewrite NZmul_0_l; now rewrite NZmul_0_r.
intro. rewrite NZmul_succ_l; rewrite NZmul_succ_r. now rewrite NZadd_cancel_r.
Qed.

Theorem NZmul_add_distr_r : forall n m p : NZ, (n + m) * p == n * p + m * p.
Proof.
intros n m p; NZinduct n.
rewrite NZmul_0_l. now do 2 rewrite NZadd_0_l.
intro n. rewrite NZadd_succ_l. do 2 rewrite NZmul_succ_l.
rewrite <- (NZadd_assoc (n * p) p (m * p)).
rewrite (NZadd_comm p (m * p)). rewrite (NZadd_assoc (n * p) (m * p) p).
now rewrite NZadd_cancel_r.
Qed.

Theorem NZmul_add_distr_l : forall n m p : NZ, n * (m + p) == n * m + n * p.
Proof.
intros n m p.
rewrite (NZmul_comm n (m + p)). rewrite (NZmul_comm n m).
rewrite (NZmul_comm n p). apply NZmul_add_distr_r.
Qed.

Theorem NZmul_assoc : forall n m p : NZ, n * (m * p) == (n * m) * p.
Proof.
intros n m p; NZinduct n.
now do 3 rewrite NZmul_0_l.
intro n. do 2 rewrite NZmul_succ_l. rewrite NZmul_add_distr_r.
now rewrite NZadd_cancel_r.
Qed.

Theorem NZmul_1_l : forall n : NZ, 1 * n == n.
Proof.
intro n. rewrite NZmul_succ_l; rewrite NZmul_0_l. now rewrite NZadd_0_l.
Qed.

Theorem NZmul_1_r : forall n : NZ, n * 1 == n.
Proof.
intro n; rewrite NZmul_comm; apply NZmul_1_l.
Qed.

End NZTimesPropFunct.

