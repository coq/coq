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

Lemma even_div2 : forall n, even n -> div2 n = div2 (S n)
with odd_div2 : forall n, odd n -> S (div2 n) = div2 (S n).
Proof.
  destruct n; intro H.
    (* 0 *) trivial.
    (* S n *) inversion_clear H. apply odd_div2 in H0 as <-. trivial.
  destruct n; intro.
    (* 0 *) inversion H.
    (* S n *) inversion_clear H. apply even_div2 in H0 as <-. trivial.
Qed.

Lemma div2_even : forall n, div2 n = div2 (S n) -> even n
with div2_odd : forall n, S (div2 n) = div2 (S n) -> odd n.
Proof.
  destruct n; intro H.
    (* 0 *) constructor.
    (* S n *) constructor. apply div2_odd. rewrite H. trivial.
  destruct n; intro H.
    (* 0 *) discriminate.
    (* S n *) constructor. apply div2_even. injection H as <-. trivial.
Qed.

Hint Resolve even_div2 div2_even odd_div2 div2_odd: arith.

Lemma even_odd_div2 :
  forall n,
    (even n <-> div2 n = div2 (S n)) /\ (odd n <-> S (div2 n) = div2 (S n)).
Proof.
  auto decomp using div2_odd, div2_even, odd_div2, even_div2.
Qed.



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
  intros. destruct H as ((IH1,IH2),(IH3,IH4)).
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
