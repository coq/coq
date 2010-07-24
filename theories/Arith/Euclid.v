(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Mult.
Require Import Compare_dec.
Require Import Wf_nat.

Open Local Scope nat_scope.

Implicit Types a b n q r : nat.

Inductive diveucl a b : Set :=
  divex : forall q r, b > r -> a = q * b + r -> diveucl a b.


Lemma eucl_dev : forall n, n > 0 -> forall m:nat, diveucl m n.
Proof.
  intros b H a; pattern a in |- *; apply gt_wf_rec; intros n H0.
  elim (le_gt_dec b n).
  intro lebn.
  elim (H0 (n - b)); auto with arith.
  intros q r g e.
  apply divex with (S q) r; simpl in |- *; auto with arith.
  elim plus_assoc.
  elim e; auto with arith.
  intros gtbn.
  apply divex with 0 n; simpl in |- *; auto with arith.
Qed.

Lemma quotient :
  forall n,
    n > 0 ->
    forall m:nat, {q : nat |  exists r : nat, m = q * n + r /\ n > r}.
Proof.
  intros b H a; pattern a in |- *; apply gt_wf_rec; intros n H0.
  elim (le_gt_dec b n).
  intro lebn.
  elim (H0 (n - b)); auto with arith.
  intros q Hq; exists (S q).
  elim Hq; intros r Hr.
  exists r; simpl in |- *; elim Hr; intros.
  elim plus_assoc.
  elim H1; auto with arith.
  intros gtbn.
  exists 0; exists n; simpl in |- *; auto with arith.
Qed.

Lemma modulo :
  forall n,
    n > 0 ->
    forall m:nat, {r : nat |  exists q : nat, m = q * n + r /\ n > r}.
Proof.
  intros b H a; pattern a in |- *; apply gt_wf_rec; intros n H0.
  elim (le_gt_dec b n).
  intro lebn.
  elim (H0 (n - b)); auto with arith.
  intros r Hr; exists r.
  elim Hr; intros q Hq.
  elim Hq; intros; exists (S q); simpl in |- *.
  elim plus_assoc.
  elim H1; auto with arith.
  intros gtbn.
  exists n; exists 0; simpl in |- *; auto with arith.
Qed.
