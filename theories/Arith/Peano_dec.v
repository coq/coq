(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Decidable PeanoNat.
Require Eqdep_dec.
Local Open Scope nat_scope.

Implicit Types m n x y : nat.

Theorem O_or_S n : {m : nat | S m = n} + {0 = n}.
Proof.
  induction n.
  - now right.
  - left; exists n; auto.
Defined.

Notation eq_nat_dec := Nat.eq_dec (only parsing).

Hint Resolve O_or_S eq_nat_dec: arith.

Theorem dec_eq_nat n m : decidable (n = m).
Proof.
  elim (Nat.eq_dec n m); [left|right]; trivial.
Defined.

Definition UIP_nat:= Eqdep_dec.UIP_dec Nat.eq_dec.

Import EqNotations.

Lemma le_unique: forall m n (le_mn1 le_mn2 : m <= n), le_mn1 = le_mn2.
Proof.
intros m n.
generalize (eq_refl (S n)).
generalize n at -1.
induction (S n) as [|n0 IHn0]; try discriminate.
clear n; intros n [= <-] le_mn1 le_mn2.
pose (def_n2 := eq_refl n0); transitivity (eq_ind _ _ le_mn2 _ def_n2).
  2: reflexivity.
generalize def_n2; revert le_mn1 le_mn2.
generalize n0 at 1 4 5 7; intros n1 le_mn1.
destruct le_mn1; intros le_mn2; destruct le_mn2.
+ now intros def_n0; rewrite (UIP_nat _ _ def_n0 eq_refl).
+ intros def_n0; generalize le_mn2; rewrite <-def_n0; intros le_mn0.
  now destruct (Nat.nle_succ_diag_l _ le_mn0).
+ intros def_n0; generalize le_mn1; rewrite def_n0; intros le_mn0.
  now destruct (Nat.nle_succ_diag_l _ le_mn0).
+ intros def_n0. injection def_n0 as ->.
  rewrite (UIP_nat _ _ def_n0 eq_refl); simpl.
  assert (H : le_mn1 = le_mn2).
    now apply IHn0.
now rewrite H.
Qed.

(** For compatibility *)
Require Import Le Lt.
