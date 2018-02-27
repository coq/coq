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

Generalizable Variables A B C D R S T U l eqA eqB eqC eqD.

Set Universe Polymorphism.

Definition crelation (A : Type) := A -> A -> Type.

Definition arrow (A B : Type) := A -> B.

Definition flip {A B C : Type} (f : A -> B -> C) := fun x y => f y x.

Definition iffT (A B : Type) := ((A -> B) * (B -> A))%type.

(** We allow to unfold the [crelation] definition while doing morphism search. *)

Section Defs.
  Context {A : Type}.

  (** We rebind crelational properties in separate classes to be able to overload each proof. *)

  Class Reflexive (R : crelation A) :=
    reflexivity : forall x : A, R x x.

  Definition complement (R : crelation A) : crelation A := 
    fun x y => R x y -> False.

  (** Opaque for proof-search. *)
  Typeclasses Opaque complement iffT.
  
  (** These are convertible. *)
  Lemma complement_inverse R : complement (flip R) = flip (complement R).
  Proof. reflexivity. Qed.

  Class Irreflexive (R : crelation A) :=
    irreflexivity : Reflexive (complement R).

  Class Symmetric (R : crelation A) :=
    symmetry : forall {x y}, R x y -> R y x.
  
  Class Asymmetric (R : crelation A) :=
    asymmetry : forall {x y}, R x y -> (complement R y x : Type).
  
  Class Transitive (R : crelation A) :=
    transitivity : forall {x y z}, R x y -> R y z -> R x z.

  (** Various combinations of reflexivity, symmetry and transitivity. *)
  
  (** A [PreOrder] is both Reflexive and Transitive. *)

  Class PreOrder (R : crelation A)  := {
    PreOrder_Reflexive :> Reflexive R | 2 ;
    PreOrder_Transitive :> Transitive R | 2 }.

  (** A [StrictOrder] is both Irreflexive and Transitive. *)

  Class StrictOrder (R : crelation A)  := {
    StrictOrder_Irreflexive :> Irreflexive R ;
    StrictOrder_Transitive :> Transitive R }.

  (** By definition, a strict order is also asymmetric *)
  Global Instance StrictOrder_Asymmetric `(StrictOrder R) : Asymmetric R.
  Proof. firstorder. Qed.

  (** A partial equivalence crelation is Symmetric and Transitive. *)
  
  Class PER (R : crelation A)  := {
    PER_Symmetric :> Symmetric R | 3 ;
    PER_Transitive :> Transitive R | 3 }.

  (** Equivalence crelations. *)

  Class Equivalence (R : crelation A)  := {
    Equivalence_Reflexive :> Reflexive R ;
    Equivalence_Symmetric :> Symmetric R ;
    Equivalence_Transitive :> Transitive R }.

  (** An Equivalence is a PER plus reflexivity. *)
  
  Global Instance Equivalence_PER {R} `(Equivalence R) : PER R | 10 :=
    { PER_Symmetric := Equivalence_Symmetric ;
      PER_Transitive := Equivalence_Transitive }.

  (** We can now define antisymmetry w.r.t. an equivalence crelation on the carrier. *)
  
  Class Antisymmetric eqA `{equ : Equivalence eqA} (R : crelation A) :=
    antisymmetry : forall {x y}, R x y -> R y x -> eqA x y.

  Class subrelation (R R' : crelation A) :=
    is_subrelation : forall {x y}, R x y -> R' x y.
  
  (** Any symmetric crelation is equal to its inverse. *)
  
  Lemma subrelation_symmetric R `(Symmetric R) : subrelation (flip R) R.
  Proof. hnf. intros x y H'. red in H'. apply symmetry. assumption. Qed.

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


  (** Rewrite crelation on a given support: declares a crelation as a rewrite
   crelation for use by the generalized rewriting tactic.
   It helps choosing if a rewrite should be handled
   by the generalized or the regular rewriting tactic using leibniz equality.
   Users can declare an [RewriteRelation A RA] anywhere to declare default
   crelations. This is also done automatically by the [Declare Relation A RA]
   commands. *)

  Class RewriteRelation (RA : crelation A).

  (** Any [Equivalence] declared in the context is automatically considered
   a rewrite crelation. *)
    
  Global Instance equivalence_rewrite_crelation `(Equivalence eqA) : RewriteRelation eqA.

  (** Leibniz equality. *)
  Section Leibniz.
    Global Instance eq_Reflexive : Reflexive (@eq A) := @eq_refl A.
    Global Instance eq_Symmetric : Symmetric (@eq A) := @eq_sym A.
    Global Instance eq_Transitive : Transitive (@eq A) := @eq_trans A.
    
    (** Leibinz equality [eq] is an equivalence crelation.
        The instance has low priority as it is always applicable
        if only the type is constrained. *)
    
    Global Program Instance eq_equivalence : Equivalence (@eq A) | 10.
  End Leibniz.
  
End Defs.

(** Default rewrite crelations handled by [setoid_rewrite]. *)
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

Hint Resolve irreflexivity : ord.

Unset Implicit Arguments.

(** A HintDb for crelations. *)

Ltac solve_crelation :=
  match goal with
  | [ |- ?R ?x ?x ] => reflexivity
  | [ H : ?R ?x ?y |- ?R ?y ?x ] => symmetry ; exact H
  end.

Hint Extern 4 => solve_crelation : crelations.

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

Ltac simpl_crelation :=
  unfold flip, impl, arrow ; try reduce ; program_simpl ;
    try ( solve [ dintuition ]).

Local Obligation Tactic := simpl_crelation.

(** Logical implication. *)

Program Instance impl_Reflexive : Reflexive impl.
Program Instance impl_Transitive : Transitive impl.

(** Logical equivalence. *)

Instance iff_Reflexive : Reflexive iff := iff_refl.
Instance iff_Symmetric : Symmetric iff := iff_sym.
Instance iff_Transitive : Transitive iff := iff_trans.

(** Logical equivalence [iff] is an equivalence crelation. *)

Program Instance iff_equivalence : Equivalence iff. 
Program Instance arrow_Reflexive : Reflexive arrow.
Program Instance arrow_Transitive : Transitive arrow.

Instance iffT_Reflexive : Reflexive iffT. 
Proof. firstorder. Defined.
Instance iffT_Symmetric : Symmetric iffT. 
Proof. firstorder. Defined. 
Instance iffT_Transitive : Transitive iffT.
Proof. firstorder. Defined.

(** We now develop a generalization of results on crelations for arbitrary predicates.
   The resulting theory can be applied to homogeneous binary crelations but also to
   arbitrary n-ary predicates. *)

Local Open Scope list_scope.

(** A compact representation of non-dependent arities, with the codomain singled-out. *)

(** We define the various operations which define the algebra on binary crelations *)
Section Binary.
  Context {A : Type}.

  Definition relation_equivalence : crelation (crelation A) :=
    fun R R' => forall x y, iffT (R x y) (R' x y).

  Global Instance: RewriteRelation relation_equivalence.
  
  Definition relation_conjunction (R : crelation A) (R' : crelation A) : crelation A :=
    fun x y => prod (R x y) (R' x y).

  Definition relation_disjunction (R : crelation A) (R' : crelation A) : crelation A :=
    fun x y => sum (R x y) (R' x y).
  
  (** Relation equivalence is an equivalence, and subrelation defines a partial order. *)

  Global Instance relation_equivalence_equivalence :
    Equivalence relation_equivalence.
  Proof. split; red; unfold relation_equivalence, iffT. firstorder. 
    firstorder. 
    intros. specialize (X x0 y0). specialize (X0 x0 y0). firstorder.
  Qed.
    
  Global Instance relation_implication_preorder : PreOrder (@subrelation A).
  Proof. firstorder. Qed.

  (** *** Partial Order.
   A partial order is a preorder which is additionally antisymmetric.
   We give an equivalent definition, up-to an equivalence crelation
   on the carrier. *)

  Class PartialOrder eqA `{equ : Equivalence A eqA} R `{preo : PreOrder A R} :=
    partial_order_equivalence : relation_equivalence eqA (relation_conjunction R (flip R)).
  
  (** The equivalence proof is sufficient for proving that [R] must be a
   morphism for equivalence (see Morphisms).  It is also sufficient to
   show that [R] is antisymmetric w.r.t. [eqA] *)

  Global Instance partial_order_antisym `(PartialOrder eqA R) : ! Antisymmetric A eqA R.
  Proof with auto.
    reduce_goal.
    apply H. firstorder.
  Qed.

  Lemma PartialOrder_inverse `(PartialOrder eqA R) : PartialOrder eqA (flip R).
  Proof. unfold flip; constructor; unfold flip. intros. apply H. apply symmetry. apply X.
         unfold relation_conjunction. intros [H1 H2]. apply H. constructor; assumption. Qed.
End Binary.

Hint Extern 3 (PartialOrder (flip _)) => class_apply PartialOrder_inverse : typeclass_instances.

(** The partial order defined by subrelation and crelation equivalence. *)

(* Program Instance subrelation_partial_order : *)
(*   ! PartialOrder (crelation A) relation_equivalence subrelation. *)
(* Obligation Tactic := idtac. *)

(* Next Obligation. *)
(* Proof. *)
(*   intros x. refine (fun x => x). *)
(* Qed. *)

Typeclasses Opaque relation_equivalence.


