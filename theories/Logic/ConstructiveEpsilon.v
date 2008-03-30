(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id:$ i*)

(** This module proves the constructive description schema, which
infers the sigma-existence (i.e., [Set]-existence) of a witness to a
predicate from the regular existence (i.e., [Prop]-existence). One
requires that the underlying set is countable and that the predicate
is decidable. *)

(** Coq does not allow case analysis on sort [Set] when the goal is in
[Prop]. Therefore, one cannot eliminate [exists n, P n] in order to
show [{n : nat | P n}]. However, one can perform a recursion on an
inductive predicate in sort [Prop] so that the returning type of the
recursion is in [Set]. This trick is described in Coq'Art book, Sect.
14.2.3 and 15.4. In particular, this trick is used in the proof of
[Fix_F] in the module Coq.Init.Wf. There, recursion is done on an
inductive predicate [Acc] and the resulting type is in [Type].

The predicate [Acc] delineates elements that are accessible via a
given relation [R]. An element is accessible if there are no infinite
[R]-descending chains starting from it.

To use [Fix_F], we define a relation R and prove that if [exists n,
P n] then 0 is accessible with respect to R. Then, by induction on the
definition of [Acc R 0], we show [{n : nat | P n}]. *)

(** Based on ideas from Benjamin Werner and Jean-François Monin *)

(** Contributed by Yevgeniy Makarov *)

Require Import Arith.

Section ConstructiveIndefiniteDescription.

Variable P : nat -> Prop.

Hypothesis P_decidable : forall x : nat, {P x} + {~ P x}.

(** To find a witness of [P] constructively, we define an algorithm
that tries P on all natural numbers starting from 0 and going up. The
relation [R] describes the connection between the two successive
numbers we try. Namely, [y] is [R]-less then [x] if we try [y] after
[x], i.e., [y = S x] and [P x] is false. Then the absence of an
infinite [R]-descending chain from 0 is equivalent to the termination
of our searching algorithm. *)

Let R (x y : nat) : Prop := x = S y /\ ~ P y.

Notation Local "'acc' x" := (Acc R x) (at level 10).

Lemma P_implies_acc : forall x : nat, P x -> acc x.
Proof.
intros x H. constructor.
intros y [_ not_Px]. absurd (P x); assumption.
Qed.

Lemma P_eventually_implies_acc : forall (x : nat) (n : nat), P (n + x) -> acc x.
Proof.
intros x n; generalize x; clear x; induction n as [|n IH]; simpl.
apply P_implies_acc.
intros x H. constructor. intros y [fxy _].
apply IH. rewrite fxy.
replace (n + S x) with (S (n + x)); auto with arith.
Defined.

Corollary P_eventually_implies_acc_ex : (exists n : nat, P n) -> acc 0.
Proof.
intros H; elim H. intros x Px. apply P_eventually_implies_acc with (n := x).
replace (x + 0) with x; auto with arith.
Defined.

(** In the following statement, we use the trick with recursion on
[Acc]. This is also where decidability of [P] is used. *)

Theorem acc_implies_P_eventually : acc 0 -> {n : nat | P n}.
Proof.
intros Acc_0. pattern 0. apply Fix_F with (R := R); [| assumption].
clear Acc_0; intros x IH.
destruct (P_decidable x) as [Px | not_Px].
exists x; simpl; assumption.
set (y := S x).
assert (Ryx : R y x). unfold R; split; auto.
destruct (IH y Ryx) as [n Hn].
exists n; assumption.
Defined.

Theorem constructive_indefinite_description_nat : (exists n : nat, P n) -> {n : nat | P n}.
Proof.
intros H; apply acc_implies_P_eventually.
apply P_eventually_implies_acc_ex; assumption.
Defined.

End ConstructiveIndefiniteDescription.

Section ConstructiveEpsilon.

(** For the current purpose, we say that a set [A] is countable if
there are functions [f : A -> nat] and [g : nat -> A] such that [g] is
a left inverse of [f]. *)

Variable A : Set.
Variable f : A -> nat.
Variable g : nat -> A.

Hypothesis gof_eq_id : forall x : A, g (f x) = x.

Variable P : A -> Prop.

Hypothesis P_decidable : forall x : A, {P x} + {~ P x}.

Definition P' (x : nat) : Prop := P (g x).

Lemma P'_decidable : forall n : nat, {P' n} + {~ P' n}.
Proof.
intro n; unfold P'; destruct (P_decidable (g n)); auto.
Defined.

Lemma constructive_indefinite_description : (exists x : A, P x) -> {x : A | P x}.
Proof.
intro H. assert (H1 : exists n : nat, P' n).
destruct H as [x Hx]. exists (f x); unfold P'. rewrite gof_eq_id; assumption.
apply (constructive_indefinite_description_nat P' P'_decidable)  in H1.
destruct H1 as [n Hn]. exists (g n); unfold P' in Hn; assumption.
Defined.

Lemma constructive_definite_description : (exists! x : A, P x) -> {x : A | P x}.
Proof.
  intros; apply constructive_indefinite_description; firstorder.
Defined.

Definition constructive_epsilon (E : exists x : A, P x) : A
  := proj1_sig (constructive_indefinite_description E).

Definition constructive_epsilon_spec (E : (exists x, P x)) : P (constructive_epsilon E)
  := proj2_sig (constructive_indefinite_description E).

End ConstructiveEpsilon.

