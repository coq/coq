(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(**
* Some properties of the multiplication for modules implementing [NZBasicFunsSig']

This file defines the [NZMulProp] functor type on top of [NZAddProp]. This
functor type is meant to be [Include]d in a module implementing [NZBasicFunsSig'].

This gives the following basic lemmas:
- [mul_0_r], [mul_1_l], [mul_1_r]
- [mul_succ_r], [mul_comm]
- [mul_add_distr_r], [mul_add_distr_l]
- [mul_assoc]
- [mul_shuffle0] and [mul_shuffle3] to rearrange products of 3 terms
- [mul_shuffle1] and [mul_shuffle2] to rearrange products of 4 terms

Notice that [NZMulProp] itself [Include]s [NZAddProp].
*)

From Stdlib.Numbers.NatInt Require Import NZAxioms NZBase NZAdd.

Module Type NZMulProp (Import NZ : NZBasicFunsSig')(Import NZBase : NZBaseProp NZ).
Include NZAddProp NZ NZBase.

Theorem mul_0_r : forall n, n * 0 == 0.
Proof.
intro n; nzinduct n; intros; now nzsimpl.
Qed.

Theorem mul_succ_r : forall n m, n * (S m) == n * m + n.
Proof.
  intros n m; nzinduct n.
  - now nzsimpl.
  - intro n. nzsimpl. rewrite succ_inj_wd, <- add_assoc, (add_comm m n), add_assoc.
    now rewrite add_cancel_r.
Qed.

Global Hint Rewrite mul_0_r mul_succ_r : nz.

Theorem mul_comm : forall n m, n * m == m * n.
Proof.
  intros n m; nzinduct n.
  - now nzsimpl.
  - intro. nzsimpl. now rewrite add_cancel_r.
Qed.

Theorem mul_add_distr_r : forall n m p, (n + m) * p == n * p + m * p.
Proof.
  intros n m p; nzinduct n.
  - now nzsimpl.
  - intro n. nzsimpl. rewrite <- add_assoc, (add_comm p (m*p)), add_assoc.
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
  intros n m p; nzinduct n. - now nzsimpl.
  - intro n. nzsimpl. rewrite mul_add_distr_r.
    now rewrite add_cancel_r.
Qed.

Theorem mul_1_l : forall n, 1 * n == n.
Proof.
intro n. now nzsimpl'.
Qed.

Theorem mul_1_r : forall n, n * 1 == n.
Proof.
intro n. now nzsimpl'.
Qed.

Global Hint Rewrite mul_1_l mul_1_r : nz.

Theorem mul_shuffle0 : forall n m p, n*m*p == n*p*m.
Proof.
intros n m p. now rewrite <- 2 mul_assoc, (mul_comm m).
Qed.

Theorem mul_shuffle1 : forall n m p q, (n * m) * (p * q) == (n * p) * (m * q).
Proof.
intros n m p q. now rewrite 2 mul_assoc, (mul_shuffle0 n).
Qed.

Theorem mul_shuffle2 : forall n m p q, (n * m) * (p * q) == (n * q) * (m * p).
Proof.
intros n m p q. rewrite (mul_comm p). apply mul_shuffle1.
Qed.

Theorem mul_shuffle3 : forall n m p, n * (m * p) == m * (n * p).
Proof.
intros n m p. now rewrite mul_assoc, (mul_comm n), mul_assoc.
Qed.

End NZMulProp.
