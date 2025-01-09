(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Class A (A : Type).
#[export] Instance an: A nat := {}.

Class B (A : Type) (a : A).
#[export] Instance bn0: B nat 0 := {}.
#[export] Instance bn1: B nat 1 := {}.

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

#[export] Hint Extern 0 (_ /\ _) => constructor : typeclass_instances.

Existing Class and.

Goal exists (T : Type) (t : T), A T /\ B T t.
Proof.
  eexists. eexists. typeclasses eauto.
Defined.

#[export] Instance ab: A bool := {}. (* Backtrack on A instance *)
Goal exists (T : Type) (t : T), A T /\ B T t.
Proof.
  eexists. eexists. typeclasses eauto.
Defined.

Class C {T} `(a : A T) (t : T). 
Require Import Classes.Init.
#[export] Hint Extern 0 { x : ?A & _ } =>
  unshelve class_apply @existT : typeclass_instances.
Existing Class sigT.
Set Typeclasses Debug.
#[export] Instance can: C an 0 := {}.
(* Backtrack on instance implementation *)
Goal exists (T : Type) (t : T), { x : A T & C x t }.
Proof.
  eexists. eexists. typeclasses eauto.
Defined.

Class D T `(a: A T).
#[export] Instance: D _ an := {}.
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
Require Import Corelib.Classes.Init.

Module NTabareau.

Set Typeclasses Dependency Order.
Unset Typeclasses Iterative Deepening.
Notation "x .1" := (projT1 x).
Notation "x .2" := (projT2 x).

Parameter myType: Type. 

Class Foo (a:myType) := {}.

Class Bar (a:myType) := {}.

Class Qux (a:myType) := {}.

Parameter fooTobar : forall a (H : Foo a), {b: myType & Bar b}.

Parameter barToqux : forall a (H : Bar a), {b: myType & Qux b}.

#[export] Hint Extern 5 (Bar ?D.1) =>
    destruct D; simpl : typeclass_instances.

#[export] Hint Extern 5 (Qux ?D.1) =>
    destruct D; simpl : typeclass_instances.

#[export] Hint Extern 1 myType =>
  unshelve refine (fooTobar _ _).1 : typeclass_instances.

#[export] Hint Extern 1 myType => unshelve refine (barToqux _ _).1 : typeclass_instances.

#[export] Hint Extern 0 { x : _ & _ } => simple refine (existT _ _ _) : typeclass_instances.

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
Notation "x .1" := (projT1 x).
Notation "x .2" := (projT2 x).

Parameter myType: Type. 
Existing Class myType.

Class Foo (a:myType) := {}.

Class Bar (a:myType) := {}.

Class Qux (a:myType) := {}.

Parameter fooTobar : forall a (H : Foo a), {b: myType & Bar b}.

Parameter barToqux : forall a (H : Bar a), {b: myType & Qux b}.

#[export] Hint Extern 5 (Bar ?D.1) =>
    destruct D; simpl : typeclass_instances.

#[export] Hint Extern 5 (Qux ?D.1) =>
    destruct D; simpl : typeclass_instances.

#[export] Hint Extern 1 myType =>
  unshelve notypeclasses refine (fooTobar _ _).1 : typeclass_instances.

#[export] Hint Extern 1 myType =>
  unshelve notypeclasses refine (barToqux _ _).1 : typeclass_instances.

#[export] Hint Extern 0 { x : _ & _ } =>
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


Require Import ListDef.

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

#[export] Hint Resolve lem1 lem2 lem3 lem4: essai.

Goal
forall (l : list (nat * nat)) (n p q : nat),
not_in_list ((p, q) :: l) n -> not_in_list l n.
  intros.
  eauto with essai.
Qed.

Module StrictlyUnique.
  Inductive thing := | List.
  Module Problem.
    Class WhatIsThis (T : Type) (t : T) : Type := what_is : thing.
    Arguments what_is {T} t _.
    Instance WhatIsThis_list {X} ls : @WhatIsThis (list X) ls := List.

    Class DynamicType := { dyn_type : Type }.

    (* [WhatIsThis ls] cannot be resolved despite having a clear answer. The
       fact that the [DynamicType] instance cannot be found makes Coq abandon
       the search for [WhatIsThis] entirely. *)
    Fail Example test := Eval lazy in (fun (ls : list dyn_type) => what_is ls _) _.
  End Problem.

  Module Solution.
    (* Inform Coq that [WhatIsThis] will not/must not instantiate evars. *)
    #[local] Set Typeclasses Strict Resolution.
    (* Inform Coq that [WhatIsThis] should not backtrack. *)
    #[local] Set Typeclasses Unique Instances.
    Class WhatIsThis (T : Type) (t : T) : Type := what_is : thing.
    Arguments what_is {T} t _.
    #[local] Unset Typeclasses Strict Resolution.
    #[local] Unset Typeclasses Unique Instances.

    Instance WhatIsThis_list {X} ls : @WhatIsThis (list X) ls := List.

    Class DynamicType := { dyn_type : Type }.

    (* We can now resolve [WhatIsThis] even though we don't have a [DynamicType] *)
    Example test := Eval lazy in (fun (ls : list dyn_type) => what_is ls _) _.
  End Solution.

  Module Dependencies.
    (* Other evars can still depend on strictly unique evars by using them
       directly in their type. We must make sure to not forget those dependencies. *)

    #[local] Set Typeclasses Strict Resolution.
    #[local] Set Typeclasses Unique Instances.
    Class SU : Type := su : unit.
    Arguments su : clear implicits.
    #[local] Unset Typeclasses Strict Resolution.
    #[local] Unset Typeclasses Unique Instances.

    Instance SU_inst : SU := tt.

    Class Depends (t : unit) := {}.
    Hint Mode Depends + : typeclass_instances.

    Instance Depends_inst {t} : Depends t := {}.

    Example test := Eval lazy in (fun (s : SU) (d : Depends (su s)) => d) _ _.
  End Dependencies.
End StrictlyUnique.
