(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Nota : this file is OBSOLETE, and left only for compatibility.
    Please consider using [Nat.div2] directly, and results about it
    (see file PeanoNat). *)

Require Import PeanoNat Even.

Local Open Scope nat_scope.

Implicit Type n : nat.

(** Here we define [n/2] and prove some of its properties *)

Notation div2 := Nat.div2 (only parsing).

(** Since [div2] is recursively defined on [0], [1] and [(S (S n))], it is
    useful to prove the corresponding induction principle *)

Lemma ind_0_1_SS :
  forall P:nat -> Prop,
    P 0 -> P 1 -> (forall n, P n -> P (S (S n))) -> forall n, P n.
Proof.
  intros P H0 H1 H2.
  fix ind_0_1_SS 1.
  destruct n as [|[|n]].
  - exact H0.
  - exact H1.
  - apply H2, ind_0_1_SS.
Qed.

(** [0 <n  =>  n/2 < n] *)

Lemma lt_div2 n : 0 < n -> div2 n < n.
Proof. apply Nat.lt_div2. Qed.

Hint Resolve lt_div2: arith.

(** Properties related to the parity *)

Lemma even_div2 n : even n -> div2 n = div2 (S n).
Proof.
 rewrite Even.even_equiv. intros (p,->).
 rewrite Nat.div2_succ_double. apply Nat.div2_double.
Qed.

Lemma odd_div2 n : odd n -> S (div2 n) = div2 (S n).
Proof.
 rewrite Even.odd_equiv. intros (p,->).
 rewrite Nat.add_1_r, Nat.div2_succ_double.
 simpl. f_equal. symmetry. apply Nat.div2_double.
Qed.

Lemma div2_even n : div2 n = div2 (S n) -> even n.
Proof.
 destruct (even_or_odd n) as [Ev|Od]; trivial.
 apply odd_div2 in Od. rewrite <- Od. intro Od'.
 elim (n_Sn _ Od').
Qed.

Lemma div2_odd n : S (div2 n) = div2 (S n) -> odd n.
Proof.
 destruct (even_or_odd n) as [Ev|Od]; trivial.
 apply even_div2 in Ev. rewrite <- Ev. intro Ev'.
 symmetry in Ev'. elim (n_Sn _ Ev').
Qed.

Hint Resolve even_div2 div2_even odd_div2 div2_odd: arith.

Lemma even_odd_div2 n :
 (even n <-> div2 n = div2 (S n)) /\
 (odd n <-> S (div2 n) = div2 (S n)).
Proof.
 split; split; auto using div2_odd, div2_even, odd_div2, even_div2.
Qed.



(** Properties related to the double ([2n]) *)

Notation double := Nat.double (only parsing).

Hint Unfold double Nat.double: arith.

Lemma double_S n : double (S n) = S (S (double n)).
Proof.
  apply Nat.add_succ_r.
Qed.

Lemma double_plus n m : double (n + m) = double n + double m.
Proof.
  apply Nat.add_shuffle1.
Qed.

Hint Resolve double_S: arith.

Lemma even_odd_double n :
  (even n <-> n = double (div2 n)) /\ (odd n <-> n = S (double (div2 n))).
Proof.
  revert n. fix even_odd_double 1. destruct n as [|[|n]].
  - (* n = 0 *)
    split; split; auto with arith. inversion 1.
  - (* n = 1 *)
    split; split; auto with arith. inversion_clear 1. inversion H0.
  - (* n = (S (S n')) *)
    destruct (even_odd_double n) as ((Ev,Ev'),(Od,Od')).
    split; split; simpl div2; rewrite ?double_S.
    + inversion_clear 1. inversion_clear H0. auto.
    + injection 1. auto with arith.
    + inversion_clear 1. inversion_clear H0. auto.
    + injection 1. auto with arith.
Qed.

(** Specializations *)

Lemma even_double n : even n -> n = double (div2 n).
Proof proj1 (proj1 (even_odd_double n)).

Lemma double_even n : n = double (div2 n) -> even n.
Proof proj2 (proj1 (even_odd_double n)).

Lemma odd_double n : odd n -> n = S (double (div2 n)).
Proof proj1 (proj2 (even_odd_double n)).

Lemma double_odd n : n = S (double (div2 n)) -> odd n.
Proof proj2 (proj2 (even_odd_double n)).

Hint Resolve even_double double_even odd_double double_odd: arith.

(** Application:
    - if [n] is even then there is a [p] such that [n = 2p]
    - if [n] is odd  then there is a [p] such that [n = 2p+1]

    (Immediate: it is [n/2]) *)

Lemma even_2n : forall n, even n -> {p : nat | n = double p}.
Proof.
  intros n H. exists (div2 n). auto with arith.
Defined.

Lemma odd_S2n : forall n, odd n -> {p : nat | n = S (double p)}.
Proof.
  intros n H. exists (div2 n). auto with arith.
Defined.

(** Doubling before dividing by two brings back to the initial number. *)

Lemma div2_double n : div2 (2*n) = n.
Proof. apply Nat.div2_double. Qed.

Lemma div2_double_plus_one n : div2 (S (2*n)) = n.
Proof. apply Nat.div2_succ_double. Qed.
