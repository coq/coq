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

Require Import Arith.
Require Import Min.
Require Import Max.
Require Import NMinus.

Module NPeanoAxiomsMod <: NAxiomsSig.
Module Export NZOrdAxiomsMod <: NZOrdAxiomsSig.
Module Export NZAxiomsMod <: NZAxiomsSig.

Definition NZ := nat.
Definition NZeq := (@eq nat).
Definition NZ0 := 0.
Definition NZsucc := S.
Definition NZpred := pred.
Definition NZplus := plus.
Definition NZminus := minus.
Definition NZtimes := mult.

Theorem NZeq_equiv : equiv nat NZeq.
Proof (eq_equiv nat).

Add Relation nat NZeq
 reflexivity proved by (proj1 NZeq_equiv)
 symmetry proved by (proj2 (proj2 NZeq_equiv))
 transitivity proved by (proj1 (proj2 NZeq_equiv))
as NZeq_rel.

(* If we say "Add Relation nat (@eq nat)" instead of "Add Relation nat NZeq"
then the theorem generated for succ_wd below is forall x, succ x = succ x,
which does not match the axioms in NAxiomsSig *)

Add Morphism NZsucc with signature NZeq ==> NZeq as NZsucc_wd.
Proof.
congruence.
Qed.

Add Morphism NZpred with signature NZeq ==> NZeq as NZpred_wd.
Proof.
congruence.
Qed.

Add Morphism NZplus with signature NZeq ==> NZeq ==> NZeq as NZplus_wd.
Proof.
congruence.
Qed.

Add Morphism NZminus with signature NZeq ==> NZeq ==> NZeq as NZminus_wd.
Proof.
congruence.
Qed.

Add Morphism NZtimes with signature NZeq ==> NZeq ==> NZeq as NZtimes_wd.
Proof.
congruence.
Qed.

Theorem NZinduction :
  forall A : nat -> Prop, predicate_wd (@eq nat) A ->
    A 0 -> (forall n : nat, A n <-> A (S n)) -> forall n : nat, A n.
Proof.
intros A A_wd A0 AS. apply nat_ind. assumption. intros; now apply -> AS.
Qed.

Theorem NZpred_succ : forall n : nat, pred (S n) = n.
Proof.
reflexivity.
Qed.

Theorem NZplus_0_l : forall n : nat, 0 + n = n.
Proof.
reflexivity.
Qed.

Theorem NZplus_succ_l : forall n m : nat, (S n) + m = S (n + m).
Proof.
reflexivity.
Qed.

Theorem NZminus_0_r : forall n : nat, n - 0 = n.
Proof.
intro n; now destruct n.
Qed.

Theorem NZminus_succ_r : forall n m : nat, n - (S m) = pred (n - m).
Proof.
intros n m; induction n m using nat_double_ind; simpl; auto. apply NZminus_0_r.
Qed.

Theorem NZtimes_0_l : forall n : nat, 0 * n = 0.
Proof.
reflexivity.
Qed.

Theorem NZtimes_succ_l : forall n m : nat, S n * m = n * m + m.
Proof.
intros n m; now rewrite plus_comm.
Qed.

End NZAxiomsMod.

Definition NZlt := lt.
Definition NZle := le.
Definition NZmin := min.
Definition NZmax := max.

Add Morphism NZlt with signature NZeq ==> NZeq ==> iff as NZlt_wd.
Proof.
unfold NZeq; intros x1 x2 H1 y1 y2 H2; rewrite H1; now rewrite H2.
Qed.

Add Morphism NZle with signature NZeq ==> NZeq ==> iff as NZle_wd.
Proof.
unfold NZeq; intros x1 x2 H1 y1 y2 H2; rewrite H1; now rewrite H2.
Qed.

Add Morphism NZmin with signature NZeq ==> NZeq ==> NZeq as NZmin_wd.
Proof.
congruence.
Qed.

Add Morphism NZmax with signature NZeq ==> NZeq ==> NZeq as NZmax_wd.
Proof.
congruence.
Qed.

Theorem NZlt_eq_cases : forall n m : nat, n <= m <-> n < m \/ n = m.
Proof.
intros n m; split.
apply le_lt_or_eq.
intro H; destruct H as [H | H].
now apply lt_le_weak. rewrite H; apply le_refl.
Qed.

Theorem NZlt_irrefl : forall n : nat, ~ (n < n).
Proof.
exact lt_irrefl.
Qed.

Theorem NZlt_succ_r : forall n m : nat, n < S m <-> n <= m.
Proof.
intros n m; split; [apply lt_n_Sm_le | apply le_lt_n_Sm].
Qed.

Theorem NZmin_l : forall n m : nat, n <= m -> NZmin n m = n.
Proof.
exact min_l.
Qed.

Theorem NZmin_r : forall n m : nat, m <= n -> NZmin n m = m.
Proof.
exact min_r.
Qed.

Theorem NZmax_l : forall n m : nat, m <= n -> NZmax n m = n.
Proof.
exact max_l.
Qed.

Theorem NZmax_r : forall n m : nat, n <= m -> NZmax n m = m.
Proof.
exact max_r.
Qed.

End NZOrdAxiomsMod.

Definition recursion : forall A : Set, A -> (nat -> A -> A) -> nat -> A :=
  fun A : Set => nat_rec (fun _ => A).
Implicit Arguments recursion [A].

Theorem succ_neq_0 : forall n : nat, S n <> 0.
Proof.
intros; discriminate.
Qed.

Theorem pred_0 : pred 0 = 0.
Proof.
reflexivity.
Qed.

Theorem recursion_wd : forall (A : Set) (Aeq : relation A),
  forall a a' : A, Aeq a a' ->
    forall f f' : nat -> A -> A, fun2_eq (@eq nat) Aeq Aeq f f' ->
      forall n n' : nat, n = n' ->
        Aeq (recursion a f n) (recursion a' f' n').
Proof.
unfold fun2_eq; induction n; intros n' Enn'; rewrite <- Enn' in *; simpl; auto.
Qed.

Theorem recursion_0 :
  forall (A : Set) (a : A) (f : nat -> A -> A), recursion a f 0 = a.
Proof.
reflexivity.
Qed.

Theorem recursion_succ :
  forall (A : Set) (Aeq : relation A) (a : A) (f : nat -> A -> A),
    Aeq a a -> fun2_wd (@eq nat) Aeq Aeq f ->
      forall n : nat, Aeq (recursion a f (S n)) (f n (recursion a f n)).
Proof.
induction n; simpl; auto.
Qed.

End NPeanoAxiomsMod.

(* Now we apply the largest property functor *)

Module Export NPeanoMinusPropMod := NMinusPropFunct NPeanoAxiomsMod.

