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

(** * Typeclass-based relations, tactics and standard instances

   This is the basic theory needed to formalize morphisms and setoids.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

Require Export Coq.Classes.Init.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relation_Definitions.

Generalizable Variables A B C D R S T U l eqA eqB eqC eqD.

(** We allow to unfold the [relation] definition while doing morphism search. *)

Section Defs.
  Context {A : Type}.

  (** We rebind relational properties in separate classes to be able to overload each proof. *)

  Class Reflexive (R : relation A) :=
    reflexivity : forall x : A, R x x.

  Definition complement (R : relation A) : relation A := fun x y => R x y -> False.

  (** Opaque for proof-search. *)
  Typeclasses Opaque complement.
  
  (** These are convertible. *)
  Lemma complement_inverse R : complement (flip R) = flip (complement R).
  Proof. reflexivity. Qed.

  Class Irreflexive (R : relation A) :=
    irreflexivity : Reflexive (complement R).

  Class Symmetric (R : relation A) :=
    symmetry : forall {x y}, R x y -> R y x.
  
  Class Asymmetric (R : relation A) :=
    asymmetry : forall {x y}, R x y -> R y x -> False.
  
  Class Transitive (R : relation A) :=
    transitivity : forall {x y z}, R x y -> R y z -> R x z.

  (** Various combinations of reflexivity, symmetry and transitivity. *)
  
  (** A [PreOrder] is both Reflexive and Transitive. *)
  
  Class PreOrder (R : relation A) : Prop := {
    PreOrder_Reflexive :> Reflexive R | 2 ;
    PreOrder_Transitive :> Transitive R | 2 }.

  (** A [StrictOrder] is both Irreflexive and Transitive. *)

  Class StrictOrder (R : relation A) : Prop := {
    StrictOrder_Irreflexive :> Irreflexive R ;
    StrictOrder_Transitive :> Transitive R }.

  (** By definition, a strict order is also asymmetric *)
  Global Instance StrictOrder_Asymmetric `(StrictOrder R) : Asymmetric R.
  Proof. firstorder. Qed.

  (** A partial equivalence relation is Symmetric and Transitive. *)
  
  Class PER (R : relation A) : Prop := {
    PER_Symmetric :> Symmetric R | 3 ;
    PER_Transitive :> Transitive R | 3 }.

  (** Equivalence relations. *)

  Class Equivalence (R : relation A) : Prop := {
    Equivalence_Reflexive :> Reflexive R ;
    Equivalence_Symmetric :> Symmetric R ;
    Equivalence_Transitive :> Transitive R }.

  (** An Equivalence is a PER plus reflexivity. *)
  
  Global Instance Equivalence_PER {R} `(E:Equivalence R) : PER R | 10 :=
    { }. 

  (** An Equivalence is a PreOrder plus symmetry. *)

  Global Instance Equivalence_PreOrder {R} `(E:Equivalence R) : PreOrder R | 10 :=
    { }.

  (** We can now define antisymmetry w.r.t. an equivalence relation on the carrier. *)
  
  Class Antisymmetric eqA `{equ : Equivalence eqA} (R : relation A) :=
    antisymmetry : forall {x y}, R x y -> R y x -> eqA x y.

  Class subrelation (R R' : relation A) : Prop :=
    is_subrelation : forall {x y}, R x y -> R' x y.
  
  (** Any symmetric relation is equal to its inverse. *)
  
  Lemma subrelation_symmetric R `(Symmetric R) : subrelation (flip R) R.
  Proof. hnf. intros. red in H0. apply symmetry. assumption. Qed.

  Section flip.
  
    Lemma flip_Reflexive `{Reflexive R} : Reflexive (flip R).
    Proof. tauto. Qed.
    
    Program Definition flip_Irreflexive `(Irreflexive R) : Irreflexive (flip R) :=
      irreflexivity (R:=R).
    
    Program Definition flip_Symmetric `(Symmetric R) : Symmetric (flip R) :=
      fun x y H => symmetry (R:=R) H.
    
    Program Definition flip_Asymmetric `(Asymmetric R) : Asymmetric (flip R) :=
      fun x y H H' => asymmetry (R:=R) H H'.
    
    Program Definition flip_Transitive `(Transitive R) : Transitive (flip R) :=
      fun x y z H H' => transitivity (R:=R) H' H.

    Program Definition flip_Antisymmetric `(Antisymmetric eqA R) :
      Antisymmetric eqA (flip R).
    Proof. firstorder. Qed.

    (** Inversing the larger structures *)

    Lemma flip_PreOrder `(PreOrder R) : PreOrder (flip R).
    Proof. firstorder. Qed.

    Lemma flip_StrictOrder `(StrictOrder R) : StrictOrder (flip R).
    Proof. firstorder. Qed.

    Lemma flip_PER `(PER R) : PER (flip R).
    Proof. firstorder. Qed.

    Lemma flip_Equivalence `(Equivalence R) : Equivalence (flip R).
    Proof. firstorder. Qed.

  End flip.

  Section complement.

    Definition complement_Irreflexive `(Reflexive R)
      : Irreflexive (complement R).
    Proof. firstorder. Qed.

    Definition complement_Symmetric `(Symmetric R) : Symmetric (complement R).
    Proof. firstorder. Qed.
  End complement.


  (** Rewrite relation on a given support: declares a relation as a rewrite
   relation for use by the generalized rewriting tactic.
   It helps choosing if a rewrite should be handled
   by the generalized or the regular rewriting tactic using leibniz equality.
   Users can declare an [RewriteRelation A RA] anywhere to declare default
   relations. This is also done automatically by the [Declare Relation A RA]
   commands. *)

  Class RewriteRelation (RA : relation A).

  (** Any [Equivalence] declared in the context is automatically considered
   a rewrite relation. *)
    
  Global Instance equivalence_rewrite_relation `(Equivalence eqA) : RewriteRelation eqA.

  (** Leibniz equality. *)
  Section Leibniz.
    Global Instance eq_Reflexive : Reflexive (@eq A) := @eq_refl A.
    Global Instance eq_Symmetric : Symmetric (@eq A) := @eq_sym A.
    Global Instance eq_Transitive : Transitive (@eq A) := @eq_trans A.
    
    (** Leibinz equality [eq] is an equivalence relation.
        The instance has low priority as it is always applicable
        if only the type is constrained. *)
    
    Global Program Instance eq_equivalence : Equivalence (@eq A) | 10.
  End Leibniz.
  
End Defs.

(** Default rewrite relations handled by [setoid_rewrite]. *)
Instance: RewriteRelation impl.
Instance: RewriteRelation iff.

(** Hints to drive the typeclass resolution avoiding loops
 due to the use of full unification. *)
Hint Extern 1 (Reflexive (complement _)) => class_apply @irreflexivity : typeclass_instances.
Hint Extern 3 (Symmetric (complement _)) => class_apply complement_Symmetric : typeclass_instances.
Hint Extern 3 (Irreflexive (complement _)) => class_apply complement_Irreflexive : typeclass_instances.

Hint Extern 3 (Reflexive (flip _)) => apply flip_Reflexive : typeclass_instances.
Hint Extern 3 (Irreflexive (flip _)) => class_apply flip_Irreflexive : typeclass_instances.
Hint Extern 3 (Symmetric (flip _)) => class_apply flip_Symmetric : typeclass_instances.
Hint Extern 3 (Asymmetric (flip _)) => class_apply flip_Asymmetric : typeclass_instances.
Hint Extern 3 (Antisymmetric (flip _)) => class_apply flip_Antisymmetric : typeclass_instances.
Hint Extern 3 (Transitive (flip _)) => class_apply flip_Transitive : typeclass_instances.
Hint Extern 3 (StrictOrder (flip _)) => class_apply flip_StrictOrder : typeclass_instances.
Hint Extern 3 (PreOrder (flip _)) => class_apply flip_PreOrder : typeclass_instances.

Hint Extern 4 (subrelation (flip _) _) => 
  class_apply @subrelation_symmetric : typeclass_instances.

Arguments irreflexivity {A R Irreflexive} [x] _.
Arguments symmetry {A} {R} {_} [x] [y] _.
Arguments asymmetry {A} {R} {_} [x] [y] _ _.
Arguments transitivity {A} {R} {_} [x] [y] [z] _ _.
Arguments Antisymmetric A eqA {_} _.

Hint Resolve irreflexivity : ord.

Unset Implicit Arguments.

(** A HintDb for relations. *)

Ltac solve_relation :=
  match goal with
  | [ |- ?R ?x ?x ] => reflexivity
  | [ H : ?R ?x ?y |- ?R ?y ?x ] => symmetry ; exact H
  end.

Hint Extern 4 => solve_relation : relations.

(** We can already dualize all these properties. *)

(** * Standard instances. *)

Ltac reduce_hyp H :=
  match type of H with
    | context [ _ <-> _ ] => fail 1
    | _ => red in H ; try reduce_hyp H
  end.

Ltac reduce_goal :=
  match goal with
    | [ |- _ <-> _ ] => fail 1
    | _ => red ; intros ; try reduce_goal
  end.

Tactic Notation "reduce" "in" hyp(Hid) := reduce_hyp Hid.

Ltac reduce := reduce_goal.

Tactic Notation "apply" "*" constr(t) :=
  first [ refine t | refine (t _) | refine (t _ _) | refine (t _ _ _) | refine (t _ _ _ _) |
    refine (t _ _ _ _ _) | refine (t _ _ _ _ _ _) | refine (t _ _ _ _ _ _ _) ].

Ltac simpl_relation :=
  unfold flip, impl, arrow ; try reduce ; program_simpl ;
    try ( solve [ dintuition ]).

Local Obligation Tactic := simpl_relation.

(** Logical implication. *)

Program Instance impl_Reflexive : Reflexive impl.
Program Instance impl_Transitive : Transitive impl.

(** Logical equivalence. *)

Instance iff_Reflexive : Reflexive iff := iff_refl.
Instance iff_Symmetric : Symmetric iff := iff_sym.
Instance iff_Transitive : Transitive iff := iff_trans.

(** Logical equivalence [iff] is an equivalence relation. *)

Program Instance iff_equivalence : Equivalence iff.

(** We now develop a generalization of results on relations for arbitrary predicates.
   The resulting theory can be applied to homogeneous binary relations but also to
   arbitrary n-ary predicates. *)

Local Open Scope list_scope.

(** A compact representation of non-dependent arities, with the codomain singled-out. *)

(* Note, we do not use [list Type] because it imposes unnecessary universe constraints *)
Inductive Tlist : Type := Tnil : Tlist | Tcons : Type -> Tlist -> Tlist.
Local Infix "::" := Tcons.

Fixpoint arrows (l : Tlist) (r : Type) : Type :=
  match l with
    | Tnil => r
    | A :: l' => A -> arrows l' r
  end.

(** We can define abbreviations for operation and relation types based on [arrows]. *)

Definition unary_operation A := arrows (A::Tnil) A.
Definition binary_operation A := arrows (A::A::Tnil) A.
Definition ternary_operation A := arrows (A::A::A::Tnil) A.

(** We define n-ary [predicate]s as functions into [Prop]. *)

Notation predicate l := (arrows l Prop).

(** Unary predicates, or sets. *)

Definition unary_predicate A := predicate (A::Tnil).

(** Homogeneous binary relations, equivalent to [relation A]. *)

Definition binary_relation A := predicate (A::A::Tnil).

(** We can close a predicate by universal or existential quantification. *)

Fixpoint predicate_all (l : Tlist) : predicate l -> Prop :=
  match l with
    | Tnil => fun f => f
    | A :: tl => fun f => forall x : A, predicate_all tl (f x)
  end.

Fixpoint predicate_exists (l : Tlist) : predicate l -> Prop :=
  match l with
    | Tnil => fun f => f
    | A :: tl => fun f => exists x : A, predicate_exists tl (f x)
  end.

(** Pointwise extension of a binary operation on [T] to a binary operation
   on functions whose codomain is [T].
   For an operator on [Prop] this lifts the operator to a binary operation. *)

Fixpoint pointwise_extension {T : Type} (op : binary_operation T)
  (l : Tlist) : binary_operation (arrows l T) :=
  match l with
    | Tnil => fun R R' => op R R'
    | A :: tl => fun R R' =>
      fun x => pointwise_extension op tl (R x) (R' x)
  end.

(** Pointwise lifting, equivalent to doing [pointwise_extension] and closing using [predicate_all]. *)

Fixpoint pointwise_lifting (op : binary_relation Prop)  (l : Tlist) : binary_relation (predicate l) :=
  match l with
    | Tnil => fun R R' => op R R'
    | A :: tl => fun R R' =>
      forall x, pointwise_lifting op tl (R x) (R' x)
  end.

(** The n-ary equivalence relation, defined by lifting the 0-ary [iff] relation. *)

Definition predicate_equivalence {l : Tlist} : binary_relation (predicate l) :=
  pointwise_lifting iff l.

(** The n-ary implication relation, defined by lifting the 0-ary [impl] relation. *)

Definition predicate_implication {l : Tlist} :=
  pointwise_lifting impl l.

(** Notations for pointwise equivalence and implication of predicates. *)

Infix "<∙>" := predicate_equivalence (at level 95, no associativity) : predicate_scope.
Infix "-∙>" := predicate_implication (at level 70, right associativity) : predicate_scope.

Local Open Scope predicate_scope.

(** The pointwise liftings of conjunction and disjunctions.
   Note that these are [binary_operation]s, building new relations out of old ones. *)

Definition predicate_intersection := pointwise_extension and.
Definition predicate_union := pointwise_extension or.

Infix "/∙\" := predicate_intersection (at level 80, right associativity) : predicate_scope.
Infix "\∙/" := predicate_union (at level 85, right associativity) : predicate_scope.

(** The always [True] and always [False] predicates. *)

Fixpoint true_predicate {l : Tlist} : predicate l :=
  match l with
    | Tnil => True
    | A :: tl => fun _ => @true_predicate tl
  end.

Fixpoint false_predicate {l : Tlist} : predicate l :=
  match l with
    | Tnil => False
    | A :: tl => fun _ => @false_predicate tl
  end.

Notation "∙⊤∙" := true_predicate : predicate_scope.
Notation "∙⊥∙" := false_predicate : predicate_scope.

(** Predicate equivalence is an equivalence, and predicate implication defines a preorder. *)

Program Instance predicate_equivalence_equivalence : 
  Equivalence (@predicate_equivalence l).

  Next Obligation.
    induction l ; firstorder.
  Qed.
  Next Obligation.
    induction l ; firstorder.
  Qed.
  Next Obligation.
    fold pointwise_lifting.
    induction l. firstorder.
    intros. simpl in *. pose (IHl (x x0) (y x0) (z x0)).
    firstorder.
  Qed.

Program Instance predicate_implication_preorder :
  PreOrder (@predicate_implication l).
  Next Obligation.
    induction l ; firstorder.
  Qed.
  Next Obligation.
    induction l. firstorder.
    unfold predicate_implication in *. simpl in *.
    intro. pose (IHl (x x0) (y x0) (z x0)). firstorder.
  Qed.

(** We define the various operations which define the algebra on binary relations,
   from the general ones. *)

Section Binary.
  Context {A : Type}.

  Definition relation_equivalence : relation (relation A) :=
    @predicate_equivalence (_::_::Tnil).

  Global Instance: RewriteRelation relation_equivalence.
  
  Definition relation_conjunction (R : relation A) (R' : relation A) : relation A :=
    @predicate_intersection (A::A::Tnil) R R'.

  Definition relation_disjunction (R : relation A) (R' : relation A) : relation A :=
    @predicate_union (A::A::Tnil) R R'.
  
  (** Relation equivalence is an equivalence, and subrelation defines a partial order. *)

  Global Instance relation_equivalence_equivalence :
    Equivalence relation_equivalence.
  Proof. exact (@predicate_equivalence_equivalence (A::A::Tnil)). Qed.
  
  Global Instance relation_implication_preorder : PreOrder (@subrelation A).
  Proof. exact (@predicate_implication_preorder (A::A::Tnil)). Qed.

  (** *** Partial Order.
   A partial order is a preorder which is additionally antisymmetric.
   We give an equivalent definition, up-to an equivalence relation
   on the carrier. *)

  Class PartialOrder eqA `{equ : Equivalence A eqA} R `{preo : PreOrder A R} :=
    partial_order_equivalence : relation_equivalence eqA (relation_conjunction R (flip R)).
  
  (** The equivalence proof is sufficient for proving that [R] must be a
   morphism for equivalence (see Morphisms).  It is also sufficient to
   show that [R] is antisymmetric w.r.t. [eqA] *)

  Global Instance partial_order_antisym `(PartialOrder eqA R) : ! Antisymmetric A eqA R.
  Proof with auto.
    reduce_goal.
    pose proof partial_order_equivalence as poe. do 3 red in poe.
    apply <- poe. firstorder.
  Qed.


  Lemma PartialOrder_inverse `(PartialOrder eqA R) : PartialOrder eqA (flip R).
  Proof. firstorder. Qed.
End Binary.

Hint Extern 3 (PartialOrder (flip _)) => class_apply PartialOrder_inverse : typeclass_instances.

(** The partial order defined by subrelation and relation equivalence. *)

Program Instance subrelation_partial_order :
  ! PartialOrder (relation A) relation_equivalence subrelation.

Next Obligation.
Proof.
  unfold relation_equivalence in *. compute; firstorder.
Qed.

Typeclasses Opaque arrows predicate_implication predicate_equivalence
            relation_equivalence pointwise_lifting.
