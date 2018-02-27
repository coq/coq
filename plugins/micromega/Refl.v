(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
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

Lemma not_make_conj_cons : forall (A:Type) (t:A) a eval  (no_middle_eval : (eval t) \/ ~ (eval  t)),
  ~ make_conj  eval (t ::a) -> ~  (eval t) \/ (~ make_conj  eval a).
Proof.
  intros.
  simpl in H.
  destruct a.
  tauto.
  tauto.
Qed.

Lemma not_make_conj_app : forall (A:Type) (t:list A) a eval
  (no_middle_eval : forall d, eval d \/ ~ eval d) ,
  ~ make_conj  eval (t ++ a) -> (~ make_conj  eval t) \/ (~ make_conj eval a).
Proof.
  induction t.
  simpl.
  tauto.
  intros.
  simpl ((a::t)++a0)in H.
  destruct (@not_make_conj_cons _ _ _ _  (no_middle_eval a) H).
  left ; red ; intros.
  apply H0.
  rewrite  make_conj_cons in H1.
  tauto.
  destruct (IHt _ _ no_middle_eval H0).
  left ; red ; intros.
  apply H1.
  rewrite make_conj_cons in H2.
  tauto.
  right ; auto.
Qed.
