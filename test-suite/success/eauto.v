(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Class A (A : Type).
  Instance an: A nat.

Class B (A : Type) (a : A).
Instance bn0: B nat 0.
Instance bn1: B nat 1.

Goal A nat.
Proof.
  typeclasses eauto.
Qed.

Goal B nat 2.
Proof.
  Fail typeclasses eauto.
Abort.

Goal exists T : Type, A T.
Proof.
  eexists. typeclasses eauto.
Defined.

Hint Extern 0 (_ /\ _) => constructor : typeclass_instances.

Existing Class and.

Goal exists (T : Type) (t : T), A T /\ B T t.
Proof.
  eexists. eexists. typeclasses eauto.
Defined.

Instance ab: A bool. (* Backtrack on A instance *)
Goal exists (T : Type) (t : T), A T /\ B T t.
Proof.
  eexists. eexists. typeclasses eauto.
Defined.

Class C {T} `(a : A T) (t : T). 
Require Import Classes.Init.
Hint Extern 0 { x : ?A & _ } =>
  unshelve class_apply @existT : typeclass_instances.
Existing Class sigT.
Set Typeclasses Debug.
Instance can: C an 0.
(* Backtrack on instance implementation *)
Goal exists (T : Type) (t : T), { x : A T & C x t }.
Proof.
  eexists. eexists. typeclasses eauto.
Defined.

Class D T `(a: A T).
  Instance: D _ an.
Goal exists (T : Type), { x : A T & D T x }.
Proof.
  eexists. typeclasses eauto.
Defined.
  

(* Example from Nicolas Magaud on coq-club - Jul 2000 *)

Definition Nat : Set := nat.
Parameter S' : Nat -> Nat.
Parameter plus' : Nat -> Nat -> Nat.

Lemma simpl_plus_l_rr1 :
 (forall n0 : Nat,
  (forall m p : Nat, plus' n0 m = plus' n0 p -> m = p) ->
  forall m p : Nat, S' (plus' n0 m) = S' (plus' n0 p) -> m = p) ->
 forall n : Nat,
 (forall m p : Nat, plus' n m = plus' n p -> m = p) ->
 forall m p : Nat, S' (plus' n m) = S' (plus' n p) -> m = p.
  intros.
  apply H0. apply f_equal_nat.
  Time info_eauto.
  Undo.
  Set Typeclasses Debug.
  Set Typeclasses Iterative Deepening.
  Time typeclasses eauto 6 with nocore. Show Proof.
  Undo.
  Time eauto. (* does EApply H *)
Qed.

(* Example from Nicolas Tabareau on coq-club - Feb 2016. 
  Full backtracking on dependent subgoals.
 *)
Require Import Coq.Classes.Init.

Module NTabareau.

Set Typeclasses Dependency Order.
Unset Typeclasses Iterative Deepening.
Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).

Parameter myType: Type. 

Class Foo (a:myType) := {}.

Class Bar (a:myType) := {}.

Class Qux (a:myType) := {}.

Parameter fooTobar : forall a (H : Foo a), {b: myType & Bar b}.

Parameter barToqux : forall a (H : Bar a), {b: myType & Qux b}.

Hint Extern 5 (Bar ?D.1) =>
    destruct D; simpl : typeclass_instances.

Hint Extern 5 (Qux ?D.1) =>
    destruct D; simpl : typeclass_instances.

Hint Extern 1 myType =>
  unshelve refine (fooTobar _ _).1 : typeclass_instances.

Hint Extern 1 myType => unshelve refine (barToqux _ _).1 : typeclass_instances.

Hint Extern 0 { x : _ & _ } => simple refine (existT _ _ _) : typeclass_instances.

Unset Typeclasses Debug.
Definition trivial a (H : Foo a) : {b : myType & Qux b}. 
Proof.
  Time typeclasses eauto 10 with typeclass_instances.
  Undo. Set Typeclasses Iterative Deepening.
  Time typeclasses eauto with typeclass_instances.
Defined.

End NTabareau.

Module NTabareauClasses.

Set Typeclasses Dependency Order.
Unset Typeclasses Iterative Deepening.
Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).

Parameter myType: Type. 
Existing Class myType.

Class Foo (a:myType) := {}.

Class Bar (a:myType) := {}.

Class Qux (a:myType) := {}.

Parameter fooTobar : forall a (H : Foo a), {b: myType & Bar b}.

Parameter barToqux : forall a (H : Bar a), {b: myType & Qux b}.

Hint Extern 5 (Bar ?D.1) =>
    destruct D; simpl : typeclass_instances.

Hint Extern 5 (Qux ?D.1) =>
    destruct D; simpl : typeclass_instances.

Hint Extern 1 myType =>
  unshelve notypeclasses refine (fooTobar _ _).1 : typeclass_instances.

Hint Extern 1 myType =>
  unshelve notypeclasses refine (barToqux _ _).1 : typeclass_instances.

Hint Extern 0 { x : _ & _ } =>
  unshelve notypeclasses refine (existT _ _ _) : typeclass_instances.

Unset Typeclasses Debug.

Definition trivial a (H : Foo a) : {b : myType & Qux b}. 
Proof.
  Time typeclasses eauto 10 with typeclass_instances.
  Undo. Set Typeclasses Iterative Deepening.
  (* Much faster in iteratove deepening mode *)
  Time typeclasses eauto with typeclass_instances.
Defined.

End NTabareauClasses.


Require Import List.

Parameter in_list : list (nat * nat) -> nat -> Prop.
Definition not_in_list (l : list (nat * nat)) (n : nat) : Prop :=
  ~ in_list l n.

(* Hints Unfold not_in_list. *)

Axiom
  lem1 :
    forall (l1 l2 : list (nat * nat)) (n : nat),
    not_in_list (l1 ++ l2) n -> not_in_list l1 n.

Axiom
  lem2 :
    forall (l1 l2 : list (nat * nat)) (n : nat),
    not_in_list (l1 ++ l2) n -> not_in_list l2 n.

Axiom
  lem3 :
    forall (l : list (nat * nat)) (n p q : nat),
    not_in_list ((p, q) :: l) n -> not_in_list l n.

Axiom
  lem4 :
    forall (l1 l2 : list (nat * nat)) (n : nat),
    not_in_list l1 n -> not_in_list l2 n -> not_in_list (l1 ++ l2) n.

Hint Resolve lem1 lem2 lem3 lem4: essai.

Goal
forall (l : list (nat * nat)) (n p q : nat),
not_in_list ((p, q) :: l) n -> not_in_list l n.
  intros.
  eauto with essai.
Qed.
