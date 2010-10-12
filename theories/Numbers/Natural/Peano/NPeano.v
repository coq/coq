(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Import Peano Peano_dec Compare_dec EqNat NAxioms NProperties NDiv.

(** Functions not already defined: div mod *)

Definition divF div x y := if leb y x then S (div (x-y) y) else 0.
Definition modF mod x y := if leb y x then mod (x-y) y else x.
Definition initF (_ _ : nat) := 0.

Fixpoint loop {A} (F:A->A)(i:A) (n:nat) : A :=
 match n with
  | 0 => i
  | S n => F (loop F i n)
 end.

Definition div x y := loop divF initF x x y.
Definition modulo x y := loop modF initF x x y.
Infix "/" := div : nat_scope.
Infix "mod" := modulo (at level 40, no associativity) : nat_scope.


(** * Implementation of [NAxiomsSig] by [nat] *)

Module Nat
 <: NAxiomsSig <: UsualDecidableTypeFull <: OrderedTypeFull <: TotalOrder.

(** Bi-directional induction. *)

Theorem bi_induction :
  forall A : nat -> Prop, Proper (eq==>iff) A ->
    A 0 -> (forall n : nat, A n <-> A (S n)) -> forall n : nat, A n.
Proof.
intros A A_wd A0 AS. apply nat_ind. assumption. intros; now apply -> AS.
Qed.

(** Basic operations. *)

Definition eq_equiv : Equivalence (@eq nat) := eq_equivalence.
Local Obligation Tactic := simpl_relation.
Program Instance succ_wd : Proper (eq==>eq) S.
Program Instance pred_wd : Proper (eq==>eq) pred.
Program Instance add_wd : Proper (eq==>eq==>eq) plus.
Program Instance sub_wd : Proper (eq==>eq==>eq) minus.
Program Instance mul_wd : Proper (eq==>eq==>eq) mult.

Theorem pred_succ : forall n : nat, pred (S n) = n.
Proof.
reflexivity.
Qed.

Theorem add_0_l : forall n : nat, 0 + n = n.
Proof.
reflexivity.
Qed.

Theorem add_succ_l : forall n m : nat, (S n) + m = S (n + m).
Proof.
reflexivity.
Qed.

Theorem sub_0_r : forall n : nat, n - 0 = n.
Proof.
intro n; now destruct n.
Qed.

Theorem sub_succ_r : forall n m : nat, n - (S m) = pred (n - m).
Proof.
induction n; destruct m; simpl; auto. apply sub_0_r.
Qed.

Theorem mul_0_l : forall n : nat, 0 * n = 0.
Proof.
reflexivity.
Qed.

Theorem mul_succ_l : forall n m : nat, S n * m = n * m + m.
Proof.
assert (add_S_r : forall n m, n+S m = S(n+m)) by (induction n; auto).
assert (add_comm : forall n m, n+m = m+n).
 induction n; simpl; auto. intros; rewrite add_S_r; auto.
intros n m; now rewrite add_comm.
Qed.

(** Order on natural numbers *)

Program Instance lt_wd : Proper (eq==>eq==>iff) lt.

Theorem lt_succ_r : forall n m : nat, n < S m <-> n <= m.
Proof.
unfold lt; split. apply le_S_n. induction 1; auto.
Qed.


Theorem lt_eq_cases : forall n m : nat, n <= m <-> n < m \/ n = m.
Proof.
split.
inversion 1; auto. rewrite lt_succ_r; auto.
destruct 1; [|subst; auto]. rewrite <- lt_succ_r; auto.
Qed.

Theorem lt_irrefl : forall n : nat, ~ (n < n).
Proof.
induction n. intro H; inversion H. rewrite lt_succ_r; auto.
Qed.

(** Facts specific to natural numbers, not integers. *)

Theorem pred_0 : pred 0 = 0.
Proof.
reflexivity.
Qed.

Definition recursion (A : Type) : A -> (nat -> A -> A) -> nat -> A :=
  nat_rect (fun _ => A).
Implicit Arguments recursion [A].

Instance recursion_wd (A : Type) (Aeq : relation A) :
 Proper (Aeq ==> (eq==>Aeq==>Aeq) ==> eq ==> Aeq) (@recursion A).
Proof.
intros a a' Ha f f' Hf n n' Hn. subst n'.
induction n; simpl; auto. apply Hf; auto.
Qed.

Theorem recursion_0 :
  forall (A : Type) (a : A) (f : nat -> A -> A), recursion a f 0 = a.
Proof.
reflexivity.
Qed.

Theorem recursion_succ :
  forall (A : Type) (Aeq : relation A) (a : A) (f : nat -> A -> A),
    Aeq a a -> Proper (eq==>Aeq==>Aeq) f ->
      forall n : nat, Aeq (recursion a f (S n)) (f n (recursion a f n)).
Proof.
unfold Proper, respectful in *; induction n; simpl; auto.
Qed.

(** The instantiation of operations.
    Placing them at the very end avoids having indirections in above lemmas. *)

Definition t := nat.
Definition eq := @eq nat.
Definition eqb := beq_nat.
Definition compare := nat_compare.
Definition zero := 0.
Definition succ := S.
Definition pred := pred.
Definition add := plus.
Definition sub := minus.
Definition mul := mult.
Definition lt := lt.
Definition le := le.

Definition min := min.
Definition max := max.
Definition max_l := max_l.
Definition max_r := max_r.
Definition min_l := min_l.
Definition min_r := min_r.

Definition eqb_eq := beq_nat_true_iff.
Definition compare_spec := nat_compare_spec.
Definition eq_dec := eq_nat_dec.

(** Generic Properties *)

Include NPropFunct
 <+ UsualMinMaxLogicalProperties <+ UsualMinMaxDecProperties.

(** Proofs of specification for [div] and [mod]. *)

Lemma div_mod : forall x y, y<>0 -> x = y*(x/y) + x mod y.
Proof.
 cut (forall n x y, y<>0 -> x<=n ->
       x = y*(loop divF initF n x y) + (loop modF initF n x y)).
 intros H x y Hy. apply H; auto.
 induction n.
 simpl; unfold initF; simpl. intros. nzsimpl. auto with arith.
 simpl; unfold divF at 1, modF at 1.
 intros.
 destruct (leb y x) as [ ]_eqn:L;
  [apply leb_complete in L | apply leb_complete_conv in L; now nzsimpl].
 rewrite mul_succ_r, <- add_assoc, (add_comm y), add_assoc.
 rewrite <- IHn; auto.
 symmetry; apply sub_add; auto.
 rewrite <- lt_succ_r.
 apply lt_le_trans with x; auto.
 apply sub_lt; auto. rewrite <- neq_0_lt_0; auto.
Qed.

Lemma mod_upper_bound : forall x y, y<>0 -> x mod y < y.
Proof.
 cut (forall n x y, y<>0 -> x<=n -> loop modF initF n x y < y).
 intros H x y Hy. apply H; auto.
 induction n.
 simpl; unfold initF. intros. rewrite <- neq_0_lt_0; auto.
 simpl; unfold modF at 1.
 intros.
 destruct (leb y x) as [ ]_eqn:L;
  [apply leb_complete in L | apply leb_complete_conv in L]; auto.
 apply IHn; auto.
 rewrite <- lt_succ_r.
 apply lt_le_trans with x; auto.
 apply sub_lt; auto. rewrite <- neq_0_lt_0; auto.
Qed.

Definition div := div.
Definition modulo := modulo.
Program Instance div_wd : Proper (eq==>eq==>eq) div.
Program Instance mod_wd : Proper (eq==>eq==>eq) modulo.

(** Generic properties of [div] and [mod] *)

Include NDivPropFunct.

End Nat.

(** [Nat] contains an [order] tactic for natural numbers *)

(** Note that [Nat.order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)

Section TestOrder.
 Let test : forall x y, x<=y -> y<=x -> x=y.
 Proof.
 Nat.order.
 Qed.
End TestOrder.
