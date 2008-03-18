(* -*- coq-prog-args: ("-emacs-U" "-top" "Coq.Classes.Morphisms") -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Typeclass-based morphisms with standard instances for equivalence relations.
 
   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
   91405 Orsay, France *)

(* $Id: FSetAVL_prog.v 616 2007-08-08 12:28:10Z msozeau $ *)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Export Coq.Classes.RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Morphisms.

   We now turn to the definition of [Morphism] and declare standard instances. 
   These will be used by the [clrewrite] tactic later. *)

(** Respectful morphisms. *)

Definition respectful_dep (A : Type) (R : relation A) 
  (B : A -> Type) (R' : forall x y, B x -> B y -> Prop) : relation (forall x : A, B x) := 
  fun f g => forall x y : A, R x y -> R' x y (f x) (g y).

Definition respectful A B (R : relation A) (R' : relation B) : relation (A -> B) :=
  fun f g => forall x y : A, R x y -> R' (f x) (g y).

(** Notations reminiscent of the old syntax for declaring morphisms. *)

Notation " R ++> R' " := (@respectful _ _ R R') (right associativity, at level 20).
Notation " R ==> R' " := (@respectful _ _ R R') (right associativity, at level 20).
Notation " R --> R' " := (@respectful _ _ (inverse R) R') (right associativity, at level 20).

(** A morphism on a relation [R] is an object respecting the relation (in its kernel). 
   The relation [R] will be instantiated by [respectful] and [A] by an arrow type 
   for usual morphisms. *)

Class Morphism A (R : relation A) (m : A) :=
  respect : R m m.

(** Here we build an equivalence instance for functions which relates respectful ones only. *)

Definition respecting [ Equivalence A (R : relation A), Equivalence B (R' : relation B) ] : Type := 
  { morph : A -> B | respectful R R' morph morph }.


Ltac obligations_tactic ::= program_simpl.

Program Instance [ Equivalence A R, Equivalence B R' ] => 
  respecting_equiv : Equivalence respecting
  (fun (f g : respecting) => forall (x y : A), R x y -> R' (proj1_sig f x) (proj1_sig g y)).

  Next Obligation.
  Proof.
    constructor ; intros.
    destruct x ; simpl.
    apply r ; auto.
  Qed.

  Next Obligation.
  Proof.
    constructor ; intros.
    symmetry ; apply H.
    symmetry ; auto.
  Qed.

  Next Obligation.
  Proof.
    constructor ; intros.
    transitivity (proj1_sig y y0).
    apply H ; auto.
    apply H0. reflexivity.
  Qed.

(** Can't use the definition [notT] as it gives a universe inconsistency. *)

Ltac obligations_tactic ::= program_simpl ; simpl_relation.

Program Instance not_impl_morphism :
  Morphism (Prop -> Prop) (impl --> impl) not.

Program Instance not_iff_morphism : 
  Morphism (Prop -> Prop) (iff ++> iff) not.

(** We make the type implicit, it can be infered from the relations. *)

Implicit Arguments Morphism [A].

(** We allow to unfold the relation definition while doing morphism search. *)

Typeclasses unfold relation.

(** Leibniz *)

(* Instance Morphism (eq ++> eq ++> iff) (eq (A:=A)). *)
(* Proof. intros ; constructor ; intros. *)
(*   obligations_tactic. *)
(*   subst. *)
(*   intuition. *)
(* Qed. *)

(* Program Definition arrow_morphism `A B` (m : A -> B) : Morphism (eq ++> eq) m. *)

(** Any morphism respecting some relations up to [iff] respects 
   them up to [impl] in each way. Very important instances as we need [impl]
   morphisms at the top level when we rewrite. *)

Class SubRelation A (R S : relation A) :=
  subrelation :> Morphism (S ==> R) id.

Instance iff_impl_subrelation : SubRelation Prop impl iff.
Proof.
  constructor ; red ; intros.
  tauto.
Qed.

Instance iff_inverse_impl_subrelation : SubRelation Prop (inverse impl) iff.
Proof.
  constructor ; red ; intros.
  tauto.
Qed.

Instance [ SubRelation A R₁ R₂ ] =>
  morphisms_subrelation : SubRelation (B -> A) (R ==> R₁) (R ==> R₂).
Proof.
  constructor ; repeat red. intros x y H x₁ y₁ H₁.
  destruct subrelation.
  red in respect0, H ; unfold id in *.
  apply respect0.
  apply H.
  apply H₁.
Qed.

Instance [ SubRelation A R₂ R₁ ] =>
  morphisms_subrelation_left : SubRelation (A -> B) (R₁ ==> R) (R₂ ==> R) | 3.
Proof.
  constructor ; repeat red ; intros x y H x₁ y₁ H₁.
  destruct subrelation.
  red in respect0, H ; unfold id in *.
  apply H.
  apply respect0.
  apply H₁.
Qed.

Lemma subrelation_morphism [ SubRelation A R₁ R₂, Morphism R₂ m ] : Morphism R₁ m.
Proof.
  intros.
  destruct subrelation.
  red in respect0 ; intros.
  constructor.
  unfold id in * ; apply respect0.
  apply respect.
Qed.

Inductive done : nat -> Type :=
  did : forall n : nat, done n.

Ltac subrelation_tac := 
  match goal with
    | [ H : done 1 |- @Morphism _ _ _ ] => fail
    | [ |- @Morphism _ _ _ ] => let H := fresh "H" in
      set(H:=did 1) ; eapply @subrelation_morphism
  end.

(* Hint Resolve @subrelation_morphism 4 : typeclass_instances. *)

Hint Extern 4 (@Morphism _ _ _) => subrelation_tac : typeclass_instances.

(** Logical implication [impl] is a morphism for logical equivalence. *)

Program Instance iff_iff_iff_impl_morphism : Morphism (iff ==> iff ==> iff) impl.

(* Typeclasses eauto := debug. *)

Program Instance [ ! Symmetric A R, Morphism (R ==> impl) m ] => reflexive_impl_iff : Morphism (R ==> iff) m.

  Next Obligation.
  Proof.
    split ; apply respect ; [ auto | symmetry ] ; auto.
  Qed.

(** The complement of a relation conserves its morphisms. *)

Program Instance {A} (RA : relation A) [ Morphism (RA ==> RA ==> iff) R ] => 
  complement_morphism : Morphism (RA ==> RA ==> iff) (complement R).

  Next Obligation.
  Proof.
    unfold complement ; intros.
    pose (respect).
    pose (r x y H).
    pose (r0 x0 y0 H0).
    intuition.
  Qed.

(** The inverse too. *)

Program Instance {A} (RA : relation A) [ Morphism (RA ==> RA ==> iff) R ] => 
  inverse_morphism : Morphism (RA ==> RA ==> iff) (inverse R).

  Next Obligation.
  Proof.
    unfold inverse ; unfold flip.
    apply respect ; auto.
  Qed.

Program Instance {A B C : Type} [ Morphism (RA ==> RB ==> RC) (f : A -> B -> C) ] => 
  flip_morphism : Morphism (RB ==> RA ==> RC) (flip f).

  Next Obligation.
  Proof.
    apply respect ; auto.
  Qed.

(** Every transitive relation gives rise to a binary morphism on [impl], 
   contravariant in the first argument, covariant in the second. *)

Program Instance [ ! Transitive A (R : relation A) ] => 
  trans_contra_co_morphism : Morphism (R --> R ++> impl) R.

  Next Obligation.
  Proof with auto.
    transitivity x...
    transitivity x0...
  Qed.

(** Dually... *)

Program Instance [ ! Transitive A (R : relation A) ] =>
  trans_co_contra_inv_impl_morphism : Morphism (R ++> R --> inverse impl) R.
  
  Next Obligation.
  Proof with auto.
    intros.
    destruct (trans_contra_co_morphism (R:=inverse R)).
    revert respect0.
    unfold respectful, inverse, flip, impl in * ; intros.
    eapply respect0 ; eauto.
  Qed.

(* Program Instance [ Transitive A (R : relation A), Symmetric A R ] => *)
(*   trans_sym_contra_co_inv_impl_morphism : ? Morphism (R --> R ++> inverse impl) R. *)

(*   Next Obligation. *)
(*   Proof with auto. *)
(*     trans y... *)
(*     sym... *)
(*     trans y0... *)
(*     sym... *)
(*   Qed. *)


(** Morphism declarations for partial applications. *)

Program Instance [ ! Transitive A R ] (x : A) =>
  trans_contra_inv_impl_morphism : Morphism (R --> inverse impl) (R x).

  Next Obligation.
  Proof with auto.
    transitivity y...
  Qed.

Program Instance [ ! Transitive A R ] (x : A) =>
  trans_co_impl_morphism : Morphism (R ==> impl) (R x).

  Next Obligation.
  Proof with auto.
    transitivity x0...
  Qed.

Program Instance [ ! Transitive A R, Symmetric R ] (x : A) =>
  trans_sym_co_inv_impl_morphism : Morphism (R ==> inverse impl) (R x).

  Next Obligation.
  Proof with auto.
    transitivity y...
    symmetry...
  Qed.

Program Instance [ ! Transitive A R, Symmetric R ] (x : A) =>
  trans_sym_contra_impl_morphism : Morphism (R --> impl) (R x).

  Next Obligation.
  Proof with auto.
    transitivity x0...
    symmetry...
  Qed.

Program Instance [ Equivalence A R ] (x : A) =>
  equivalence_partial_app_morphism : Morphism (R ==> iff) (R x).

  Next Obligation.
  Proof with auto.
    split. intros ; transitivity x0...
    intros.
    transitivity y...
    symmetry...
  Qed.

(** With symmetric relations, variance is no issue ! *)

(* Program Instance (A B : Type) (R : relation A) (R' : relation B) *)
(*   [ Morphism _ (R ==> R') m ] [ Symmetric A R ] =>  *)
(*   sym_contra_morphism : Morphism (R --> R') m. *)

(*   Next Obligation. *)
(*   Proof with auto. *)
(*     repeat (red ; intros). apply respect. *)
(*     sym... *)
(*   Qed. *)

(** [R] is reflexive, hence we can build the needed proof. *)

Program Instance (A B : Type) (R : relation A) (R' : relation B)
  [ Morphism (R ==> R') m ] [ Reflexive R ] (x : A) =>
  reflexive_partial_app_morphism : Morphism R' (m x) | 3.

  Next Obligation.
  Proof with auto.
    intros.
    apply (respect (m:=m))...
    reflexivity.
  Qed.

(** Every transitive relation induces a morphism by "pushing" an [R x y] on the left of an [R x z] proof
   to get an [R y z] goal. *)

Program Instance [ ! Transitive A R ] => 
  trans_co_eq_inv_impl_morphism : Morphism (R ==> (@eq A) ==> inverse impl) R.

  Next Obligation.
  Proof with auto.
    transitivity y...
    subst x0...
  Qed.

Program Instance [ ! Transitive A R ] => 
  trans_contra_eq_impl_morphism : Morphism (R --> (@eq A) ==> impl) R.

  Next Obligation.
  Proof with auto.
    transitivity x...
    subst x0...
  Qed.

(** Every symmetric and transitive relation gives rise to an equivariant morphism. *)

Program Instance [ ! Transitive A R, Symmetric R ] => 
  trans_sym_morphism : Morphism (R ==> R ==> iff) R.

  Next Obligation.
  Proof with auto.
    split ; intros.
    transitivity x0... transitivity x... symmetry...
  
    transitivity y... transitivity y0... symmetry...
  Qed.

Program Instance [ Equivalence A R ] => 
  equiv_morphism : Morphism (R ==> R ==> iff) R.

  Next Obligation.
  Proof with auto.
    split ; intros.
    transitivity x0... transitivity x... symmetry...
  
    transitivity y... transitivity y0... symmetry...
  Qed.

(** In case the rewrite happens at top level. *)

Program Instance iff_inverse_impl_id :
  Morphism (iff ==> inverse impl) id.

Program Instance inverse_iff_inverse_impl_id :
  Morphism (iff --> inverse impl) id.
  
Program Instance iff_impl_id :
  Morphism (iff ==> impl) id.

Program Instance inverse_iff_impl_id :
  Morphism (iff --> impl) id.
  
(** Standard instances for [iff] and [impl]. *)

(** Logical conjunction. *)

Program Instance and_impl_iff_morphism : 
  Morphism (impl ==> iff ==> impl) and.

Program Instance and_iff_impl_morphism : 
  Morphism (iff ==> impl ==> impl) and.

Program Instance and_inverse_impl_iff_morphism : 
  Morphism (inverse impl ==> iff ==> inverse impl) and.

Program Instance and_iff_inverse_impl_morphism : 
  Morphism (iff ==> inverse impl ==> inverse impl) and.

Program Instance and_iff_morphism : 
  Morphism (iff ==> iff ==> iff) and.

(** Logical disjunction. *)

Program Instance or_impl_iff_morphism : 
  Morphism (impl ==> iff ==> impl) or.

Program Instance or_iff_impl_morphism : 
  Morphism (iff ==> impl ==> impl) or.

Program Instance or_inverse_impl_iff_morphism :
  Morphism (inverse impl ==> iff ==> inverse impl) or.

Program Instance or_iff_inverse_impl_morphism : 
  Morphism (iff ==> inverse impl ==> inverse impl) or.

Program Instance or_iff_morphism : 
  Morphism (iff ==> iff ==> iff) or.

(** Coq functions are morphisms for leibniz equality, 
   applied only if really needed. *)

(* Instance {A B : Type} (m : A -> B) => *)
(*   any_eq_eq_morphism : Morphism (@Logic.eq A ==> @Logic.eq B) m | 4. *)
(* Proof. *)
(*   red ; intros. subst ; reflexivity. *)
(* Qed. *)

(* Instance {A : Type} (m : A -> Prop) => *)
(*   any_eq_iff_morphism : Morphism (@Logic.eq A ==> iff) m | 4. *)
(* Proof. *)
(*   red ; intros. subst ; split; trivial. *)
(* Qed. *)

Instance (A B : Type) [ ! Reflexive B R ] (m : A -> B) =>
  eq_reflexive_morphism : Morphism (@Logic.eq A ==> R) m | 3.
Proof. simpl_relation. Qed.

Instance (A B : Type) [ ! Reflexive B R' ] => 
  Reflexive (@Logic.eq A ==> R').
Proof. simpl_relation. Qed.

(** [respectful] is a morphism for relation equivalence. *)

Instance respectful_morphism : 
  Morphism (relation_equivalence ++> relation_equivalence ++> relation_equivalence) (@respectful A B). 
Proof.
  do 2 red ; intros.
  unfold respectful, relation_equivalence in *.
  red ; intros.
  split ; intros.
  
    rewrite <- H0.
    apply H1.
    rewrite H.
    assumption.

    rewrite H0.
    apply H1.
    rewrite <- H.
    assumption.
Qed.

Lemma inverse_respectful : forall (A : Type) (R : relation A) (B : Type) (R' : relation B),
  inverse (R ==> R') ==rel (inverse R ==> inverse R').
Proof.
  intros.
  unfold inverse, flip.
  unfold respectful.
  split ; intros ; intuition.
Qed.

Class (A : Type) (R : relation A) => Normalizes (m : A) (m' : A) :=
  normalizes : R m m'.

Instance (A : Type) (R : relation A) (B : Type) (R' : relation B) =>
  Normalizes relation_equivalence (inverse R ==> inverse R') (inverse (R ==> R')) .
Proof.
  symmetry ; apply inverse_respectful.
Qed.

Instance (A : Type) (R : relation A) (B : Type) (R' R'' : relation B) 
  [ Normalizes relation_equivalence R' (inverse R'') ] =>
  Normalizes relation_equivalence (inverse R ==> R') (inverse (R ==> R'')) .
Proof.
  pose normalizes.
  setoid_rewrite r.
  setoid_rewrite inverse_respectful.
  reflexivity.
Qed.

Program Instance (A : Type) (R : relation A)
  [ Morphism R m ] => morphism_inverse_morphism :
  Morphism (inverse R) m | 2.

  Next Obligation.
  Proof.
    apply respect.
  Qed.

(** Bootstrap !!! *)

Instance morphism_morphism : Morphism (relation_equivalence ==> @eq _ ==> iff) (@Morphism A).
Proof.
  simpl_relation.
  subst.
  unfold relation_equivalence in H.
  split ; constructor ; intros.
  setoid_rewrite <- H.
  apply respect.
  setoid_rewrite H.
  apply respect.
Qed.
  
Lemma morphism_releq_morphism (A : Type) (R : relation A) (R' : relation A)
  [ Normalizes relation_equivalence R R' ]
  [ Morphism R' m ] : Morphism R m.
Proof.
  intros. 
  pose respect.
  assert(n:=normalizes).
  setoid_rewrite n.
  assumption.
Qed.

Inductive normalization_done : Prop := did_normalization.

Ltac morphism_normalization := 
  match goal with
    | [ _ : normalization_done |- @Morphism _ _ _ ] => fail
    | [ |- @Morphism _ _ _ ] => let H := fresh "H" in
      set(H:=did_normalization) ; eapply @morphism_releq_morphism
  end.

Hint Extern 5 (@Morphism _ _ _) => morphism_normalization : typeclass_instances.
