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

Require Import NZAxioms NZBase NZAdd.

Module Type NZMulPropSig
 (Import NZ : NZAxiomsSig')(Import NZBase : NZBasePropSig NZ).
Include NZAddPropSig NZ NZBase.

Theorem mul_0_r : forall n, n * 0 == 0.
Proof.
nzinduct n; intros; now nzsimpl.
Qed.

Theorem mul_succ_r : forall n m, n * (S m) == n * m + n.
Proof.
intros n m; nzinduct n. now nzsimpl.
intro n. nzsimpl. rewrite succ_inj_wd, <- add_assoc, (add_comm m n), add_assoc.
now rewrite add_cancel_r.
Qed.

Hint Rewrite mul_0_r mul_succ_r : nz.

Theorem mul_comm : forall n m, n * m == m * n.
Proof.
intros n m; nzinduct n. now nzsimpl.
intro. nzsimpl. now rewrite add_cancel_r.
Qed.

Theorem mul_add_distr_r : forall n m p, (n + m) * p == n * p + m * p.
Proof.
intros n m p; nzinduct n. now nzsimpl.
intro n. nzsimpl. rewrite <- add_assoc, (add_comm p (m*p)), add_assoc.
now rewrite add_cancel_r.
Qed.

Theorem mul_add_distr_l : forall n m p, n * (m + p) == n * m + n * p.
Proof.
intros n m p.
rewrite (mul_comm n (m + p)), (mul_comm n m), (mul_comm n p).
apply mul_add_distr_r.
Qed.

Theorem mul_assoc : forall n m p, n * (m * p) == (n * m) * p.
Proof.
intros n m p; nzinduct n. now nzsimpl.
intro n. nzsimpl. rewrite mul_add_distr_r.
now rewrite add_cancel_r.
Qed.

Theorem mul_1_l : forall n, 1 * n == n.
Proof.
intro n. now nzsimpl.
Qed.

Theorem mul_1_r : forall n, n * 1 == n.
Proof.
intro n. now nzsimpl.
Qed.

End NZMulPropSig.
