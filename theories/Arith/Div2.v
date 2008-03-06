(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Lt.
Require Import Plus.
Require Import Compare_dec.
Require Import Even.

Open Local Scope nat_scope.

Implicit Type n : nat.

(** Here we define [n/2] and prove some of its properties *)

Fixpoint div2 n : nat :=
  match n with
  | O => 0
  | S O => 0
  | S (S n') => S (div2 n')
  end.

(** Since [div2] is recursively defined on [0], [1] and [(S (S n))], it is
    useful to prove the corresponding induction principle *)

Lemma ind_0_1_SS :
  forall P:nat -> Prop,
    P 0 -> P 1 -> (forall n, P n -> P (S (S n))) -> forall n, P n.
Proof.
  intros P H0 H1 Hn.
  cut (forall n, P n /\ P (S n)).
  intros H'n n. elim (H'n n). auto with arith.
  
  induction n. auto with arith.
  intros. elim IHn; auto with arith.
Qed.

(** [0 <n  =>  n/2 < n] *)

Lemma lt_div2 : forall n, 0 < n -> div2 n < n.
Proof.
  intro n. pattern n in |- *. apply ind_0_1_SS.
  (* n = 0 *)
  inversion 1.
  (* n=1 *)
  simpl; trivial.
  (* n=S S n' *)
  intro n'; case (zerop n').
    intro n'_eq_0. rewrite n'_eq_0. auto with arith.
    auto with arith.
Qed.

Hint Resolve lt_div2: arith.

(** Properties related to the parity *)

Lemma even_odd_div2 :
  forall n,
    (even n <-> div2 n = div2 (S n)) /\ (odd n <-> S (div2 n) = div2 (S n)).
Proof.
  intro n. pattern n in |- *. apply ind_0_1_SS.
  (* n  = 0 *)
  split. split; auto with arith. 
  split. intro H. inversion H.
  intro H.  absurd (S (div2 0) = div2 1); auto with arith.
  (* n = 1 *)
  split. split. intro. inversion H. inversion H1.
  intro H.  absurd (div2 1 = div2 2).
  simpl in |- *. discriminate. assumption.
  split; auto with arith.
  (* n = (S (S n')) *)
  intros. decompose [and] H. unfold iff in H0, H1.
  decompose [and] H0. decompose [and] H1. clear H H0 H1.
  split; split; auto with arith.
  intro H. inversion H. inversion H1.
  change (S (div2 n0) = S (div2 (S n0))) in |- *. auto with arith.
  intro H. inversion H. inversion H1.
  change (S (S (div2 n0)) = S (div2 (S n0))) in |- *. auto with arith.
Qed.

(** Specializations *)

Lemma even_div2 : forall n, even n -> div2 n = div2 (S n).
Proof fun n => proj1 (proj1 (even_odd_div2 n)).

Lemma div2_even : forall n, div2 n = div2 (S n) -> even n.
Proof fun n => proj2 (proj1 (even_odd_div2 n)).

Lemma odd_div2 : forall n, odd n -> S (div2 n) = div2 (S n).
Proof fun n => proj1 (proj2 (even_odd_div2 n)).

Lemma div2_odd : forall n, S (div2 n) = div2 (S n) -> odd n.
Proof fun n => proj2 (proj2 (even_odd_div2 n)).

Hint Resolve even_div2 div2_even odd_div2 div2_odd: arith.

(** Properties related to the double ([2n]) *)

Definition double n := n + n.

Hint Unfold double: arith.

Lemma double_S : forall n, double (S n) = S (S (double n)).
Proof.
  intro. unfold double in |- *. simpl in |- *. auto with arith.
Qed.

Lemma double_plus : forall n (m:nat), double (n + m) = double n + double m.
Proof.
  intros m n. unfold double in |- *.
  do 2 rewrite plus_assoc_reverse. rewrite (plus_permute n).
  reflexivity.
Qed.

Hint Resolve double_S: arith.

Lemma even_odd_double :
  forall n,
    (even n <-> n = double (div2 n)) /\ (odd n <-> n = S (double (div2 n))).
Proof.
  intro n. pattern n in |- *. apply ind_0_1_SS.
  (* n = 0 *)
  split; split; auto with arith.
  intro H. inversion H.
  (* n = 1 *)
  split; split; auto with arith.
  intro H. inversion H. inversion H1.
  (* n = (S (S n')) *)
  intros. decompose [and] H. unfold iff in H0, H1.
  decompose [and] H0. decompose [and] H1. clear H H0 H1.
  split; split.
  intro H. inversion H. inversion H1.
  simpl in |- *. rewrite (double_S (div2 n0)). auto with arith.
  simpl in |- *. rewrite (double_S (div2 n0)). intro H. injection H. auto with arith.
  intro H. inversion H. inversion H1.
  simpl in |- *. rewrite (double_S (div2 n0)). auto with arith.
  simpl in |- *. rewrite (double_S (div2 n0)). intro H. injection H. auto with arith.
Qed.


(** Specializations *)

Lemma even_double : forall n, even n -> n = double (div2 n).
Proof fun n => proj1 (proj1 (even_odd_double n)).

Lemma double_even : forall n, n = double (div2 n) -> even n.
Proof fun n => proj2 (proj1 (even_odd_double n)).

Lemma odd_double : forall n, odd n -> n = S (double (div2 n)).
Proof fun n => proj1 (proj2 (even_odd_double n)).

Lemma double_odd : forall n, n = S (double (div2 n)) -> odd n.
Proof fun n => proj2 (proj2 (even_odd_double n)).

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

Lemma div2_double : forall n:nat, div2 (2*n) = n.
Proof.
  induction n.
  simpl; auto.
  simpl.
  replace (n+S(n+0)) with (S (2*n)).
  f_equal; auto.
  simpl; auto with arith.
Qed.

Lemma div2_double_plus_one : forall n:nat, div2 (S (2*n)) = n.
Proof.
  induction n.
  simpl; auto.
  simpl.
  replace (n+S(n+0)) with (S (2*n)).
  f_equal; auto.
  simpl; auto with arith.
Qed.
