(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

Require Import List.
Require Setoid.

Set Implicit Arguments.

(* Refl of '->' '/\': basic properties *)

Fixpoint make_impl (A : Type) (eval : A -> Prop) (l : list A) (goal : Prop) {struct l} : Prop :=
  match l with
    | nil => goal
    | cons e l => (eval e) -> (make_impl eval l goal)
  end.

Theorem make_impl_true :
  forall (A : Type) (eval : A -> Prop) (l : list A), make_impl eval l True.
Proof.
induction l as [| a l IH]; simpl.
trivial.
intro; apply IH.
Qed.


Theorem make_impl_map :
  forall (A B: Type) (eval : A -> Prop) (eval' : A*B -> Prop) (l : list (A*B)) r
         (EVAL : forall x, eval' x <-> eval (fst x)),
    make_impl eval' l r <-> make_impl eval (List.map fst l) r.
Proof.
induction l as [| a l IH]; simpl.
- tauto.
- intros.
  rewrite EVAL.
  rewrite IH.
  tauto.
  auto.
Qed.

Fixpoint make_conj (A : Type) (eval : A -> Prop) (l : list A) {struct l} : Prop :=
  match l with
    | nil => True
    | cons e nil => (eval e)
    | cons e l2 => ((eval e) /\ (make_conj eval l2))
  end.

Theorem make_conj_cons : forall (A : Type) (eval : A -> Prop) (a : A) (l : list A),
  make_conj eval (a :: l) <-> eval a /\ make_conj eval l.
Proof.
intros; destruct l; simpl; tauto.
Qed.


Lemma make_conj_impl : forall (A : Type) (eval : A -> Prop) (l : list A) (g : Prop),
  (make_conj eval l -> g) <-> make_impl eval l g.
Proof.
  induction l.
  simpl.
  tauto.
  simpl.
  intros.
  destruct l.
  simpl.
  tauto.
  generalize (IHl g).
  tauto.
Qed.

Lemma make_conj_in : forall (A : Type) (eval : A -> Prop) (l : list A),
  make_conj eval l -> (forall p, In p l -> eval p).
Proof.
  induction l.
  simpl.
  tauto.
  simpl.
  intros.
  destruct l.
  simpl in H0.
  destruct H0.
  subst; auto.
  tauto.
  destruct H.
  destruct H0.
  subst;auto.
  apply IHl; auto.
Qed.

Lemma make_conj_app : forall  A eval l1 l2, @make_conj A eval (l1 ++ l2) <-> @make_conj A eval l1 /\ @make_conj A eval l2.
Proof.
  induction l1.
  simpl.
  tauto.
  intros.
  change ((a::l1) ++ l2) with (a :: (l1 ++ l2)).
  rewrite make_conj_cons.
  rewrite IHl1.
  rewrite make_conj_cons.
  tauto.
Qed.

Infix "+++" := rev_append (right associativity, at level 60) : list_scope.

Lemma make_conj_rapp : forall  A eval l1 l2, @make_conj A eval (l1 +++ l2) <-> @make_conj A eval (l1++l2).
Proof.
  induction l1.
  - simpl. tauto.
  - intros.
    simpl rev_append at 1.
    rewrite IHl1.
    rewrite make_conj_app.
    rewrite make_conj_cons.
    simpl app.
    rewrite make_conj_cons.
    rewrite make_conj_app.
    tauto.
Qed.

Lemma not_make_conj_cons : forall (A:Type) (t:A) a eval  (no_middle_eval : (eval t) \/ ~ (eval  t)),
  ~ make_conj  eval (t ::a) <-> ~  (eval t) \/ (~ make_conj  eval a).
Proof.
  intros.
  rewrite make_conj_cons.
  tauto.
Qed.

Lemma not_make_conj_app : forall (A:Type) (t:list A) a eval
  (no_middle_eval : forall d, eval d \/ ~ eval d) ,
  ~ make_conj  eval (t ++ a) <-> (~ make_conj  eval t) \/ (~ make_conj eval a).
Proof.
  induction t.
  - simpl.
    tauto.
  - intros.
    simpl ((a::t)++a0).
    rewrite !not_make_conj_cons by auto.
    rewrite IHt by auto.
    tauto.
Qed.
