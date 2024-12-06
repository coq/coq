(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import PeanoNat.
Require Import Compare_dec.
Require Import Wf_nat.

Local Open Scope nat_scope.

Implicit Types a b n q r : nat.

Inductive diveucl a b : Set :=
  divex : forall q r, b > r -> a = q * b + r -> diveucl a b.

Lemma eucl_dev : forall n, n > 0 -> forall m:nat, diveucl m n.
Proof.
  intros n H m; induction m as (m,H0) using gt_wf_rec.
  destruct (le_gt_dec n m) as [Hlebn|Hgtbn].
  - destruct (H0 (m - n)) as (q,r,Hge0,Heq); [ apply Nat.sub_lt; auto | ].
    apply divex with (S q) r; trivial.
    simpl; rewrite <- Nat.add_assoc, <- Heq, Nat.add_comm, Nat.sub_add; trivial.
  - apply divex with 0 m; simpl; trivial.
Defined.

Lemma quotient :
  forall n,
    n > 0 ->
    forall m:nat, {q : nat |  exists r : nat, m = q * n + r /\ n > r}.
Proof.
  intros n H m; induction m as (m,H0) using gt_wf_rec.
  destruct (le_gt_dec n m) as [Hlebn|Hgtbn].
  - destruct (H0 (m - n)) as (q & Hq); [ apply Nat.sub_lt; auto | ].
    exists (S q); destruct Hq as (r & Heq & Hgt); exists r; split; trivial.
    simpl; rewrite <- Nat.add_assoc, <- Heq, Nat.add_comm, Nat.sub_add; trivial.
  - exists 0; exists m; simpl; auto.
Defined.

Lemma modulo :
  forall n,
    n > 0 ->
    forall m:nat, {r : nat |  exists q : nat, m = q * n + r /\ n > r}.
Proof.
  intros n H m; induction m as (m,H0) using gt_wf_rec.
  destruct (le_gt_dec n m) as [Hlebn|Hgtbn].
  - destruct (H0 (m - n)) as (r & Hr); [ apply Nat.sub_lt; auto | ].
    exists r; destruct Hr as (q & Heq & Hgt); exists (S q); split; trivial.
    simpl; rewrite <- Nat.add_assoc, <- Heq, Nat.add_comm, Nat.sub_add; trivial.
  - exists m; exists 0; simpl; auto.
Defined.
