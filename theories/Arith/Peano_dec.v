(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Decidable.
Require Eqdep_dec.
Require Import Le Lt.
Open Local Scope nat_scope.

Implicit Types m n x y : nat.

Theorem O_or_S : forall n, {m : nat | S m = n} + {0 = n}.
Proof.
  induction n.
  auto.
  left; exists n; auto.
Defined.

Theorem eq_nat_dec : forall n m, {n = m} + {n <> m}.
Proof.
  induction n; destruct m; auto.
  elim (IHn m); auto.
Defined.

Hint Resolve O_or_S eq_nat_dec: arith.

Theorem dec_eq_nat : forall n m, decidable (n = m).
  intros x y; unfold decidable in |- *; elim (eq_nat_dec x y); auto with arith.
Defined.

Definition UIP_nat:= Eqdep_dec.UIP_dec eq_nat_dec.

Lemma le_unique: forall m n (h1 h2: m <= n), h1 = h2.
Proof.
fix 3.
refine (fun m _ h1 => match h1 as h' in _ <= k return forall hh: m <= k, h' = hh
  with le_n => _ |le_S i H => _ end).
refine (fun hh => match hh as h' in _ <= k return forall eq: m = k, 
  le_n m = match eq in _ = p return m <= p -> m <= m with |eq_refl => fun bli => bli end h' with
    |le_n => fun eq => _ |le_S j H' => fun eq => _ end eq_refl).
rewrite (UIP_nat _ _ eq eq_refl). reflexivity.
subst m. destruct (Lt.lt_irrefl j H').
refine (fun hh => match hh as h' in _ <= k return match k as k' return m <= k' -> Prop
  with |0 => fun _ => True |S i' => fun h'' => forall H':m <= i', le_S m i' H' = h'' end h'
    with |le_n => _ |le_S j H2 => fun H' => _ end H).
destruct m. exact I. intros; destruct (Lt.lt_irrefl m H').
f_equal. apply le_unique.
Qed.
