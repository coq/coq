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
Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.RelationClasses.

Open Local Scope relation_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Morphisms.

   We now turn to the definition of [Morphism] and declare standard instances. 
   These will be used by the [clrewrite] tactic later. *)

(** Respectful morphisms. *)

(** The fully dependent version, not used yet. *)

Definition respectful_hetero 
  (A B : Type) 
  (C : A -> Type) (D : B -> Type) 
  (R : A -> B -> Prop) 
  (R' : forall (x : A) (y : B), C x -> D y -> Prop) : 
    (forall x : A, C x) -> (forall x : B, D x) -> Prop := 
    fun f g => forall x y, R x y -> R' x y (f x) (g y).

(** The non-dependent version is an instance where we forget dependencies. *)

Definition respectful (A B : Type) (R : relation A) (R' : relation B) : relation (A -> B) :=
  Eval compute in @respectful_hetero A A (fun _ => B) (fun _ => B) R (fun _ _ => R').

(** Notations reminiscent of the old syntax for declaring morphisms. *)

Delimit Scope signature_scope with signature.

Notation " R ++> R' " := (@respectful _ _ (R%signature) (R'%signature)) 
  (right associativity, at level 55) : signature_scope.

Notation " R ==> R' " := (@respectful _ _ (R%signature) (R'%signature))
  (right associativity, at level 55) : signature_scope.

Notation " R --> R' " := (@respectful _ _ (inverse (R%signature)) (R'%signature))
  (right associativity, at level 55) : signature_scope.

Arguments Scope respectful [type_scope type_scope signature_scope signature_scope].

Open Local Scope signature_scope.

(** A morphism on a relation [R] is an object respecting the relation (in its kernel). 
   The relation [R] will be instantiated by [respectful] and [A] by an arrow type 
   for usual morphisms. *)

Class Morphism A (R : relation A) (m : A) : Prop :=
  respect : R m m.

Arguments Scope Morphism [type_scope signature_scope].

(** Here we build an equivalence instance for functions which relates respectful ones only. *)

Definition respecting [ Equivalence A (R : relation A), Equivalence B (R' : relation B) ] : Type := 
  { morph : A -> B | respectful R R' morph morph }.

Ltac obligations_tactic ::= program_simpl.

Program Instance [ Equivalence A R, Equivalence B R' ] => 
  respecting_equiv : Equivalence respecting
  (fun (f g : respecting) => forall (x y : A), R x y -> R' (proj1_sig f x) (proj1_sig g y)).

  Next Obligation.
  Proof.
    red ; intros.
    destruct x ; simpl.
    apply r ; auto.
  Qed.

  Next Obligation.
  Proof.
    red ; intros.
    symmetry ; apply H.
    symmetry ; auto.
  Qed.

  Next Obligation.
  Proof.
    red ; intros.
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

(** Subrelations induce a morphism on the identity, not used for morphism search yet. *)

Lemma subrelation_id_morphism [ subrelation A R₁ R₂ ] : Morphism (R₁ ==> R₂) id.
Proof. firstorder. Qed.

(** The subrelation property goes through products as usual. *)

Instance [ sub : subrelation A R₁ R₂ ] =>
  morphisms_subrelation : ! subrelation (B -> A) (R ==> R₁) (R ==> R₂).
Proof. firstorder. Qed.

Instance [ sub : subrelation A R₂ R₁ ] =>
  morphisms_subrelation_left : ! subrelation (A -> B) (R₁ ==> R) (R₂ ==> R) | 3.
Proof. firstorder. Qed.

(** [Morphism] is itself a covariant morphism for [subrelation]. *)

Lemma subrelation_morphism [ subrelation A R₁ R₂, ! Morphism R₁ m ] : Morphism R₂ m.
Proof.
  intros. apply* H. apply H0.
Qed.

Instance morphism_subrelation_morphism : 
  Morphism (subrelation ++> @eq _ ==> impl) (@Morphism A).
Proof. reduce. subst. firstorder. Qed.

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

Program Instance [ Symmetric A R, Morphism _ (R ==> impl) m ] => Reflexive_impl_iff : Morphism (R ==> iff) m.

  Next Obligation.
  Proof.
    split ; apply respect ; [ auto | symmetry ] ; auto.
  Qed.

(** The complement of a relation conserves its morphisms. *)

Program Instance [ mR : Morphism (A -> A -> Prop) (RA ==> RA ==> iff) R ] => 
  complement_morphism : Morphism (RA ==> RA ==> iff) (complement R).

  Next Obligation.
  Proof.
    unfold complement.
    pose (respect).
    pose (r x y H).
    pose (r0 x0 y0 H0).
    intuition.
  Qed.

(** The inverse too. *)

Program Instance [ Morphism (A -> _) (RA ==> RA ==> iff) R ] => 
  inverse_morphism : Morphism (RA ==> RA ==> iff) (inverse R).

  Next Obligation.
  Proof.
    apply respect ; auto.
  Qed.

Program Instance [ Morphism (A -> B -> C) (RA ==> RB ==> RC) f ] => 
  flip_morphism : Morphism (RB ==> RA ==> RC) (flip f).

  Next Obligation.
  Proof.
    apply respect ; auto.
  Qed.

(** Every Transitive relation gives rise to a binary morphism on [impl], 
   contravariant in the first argument, covariant in the second. *)

Program Instance [ Transitive A R ] => 
  trans_contra_co_morphism : Morphism (R --> R ++> impl) R.

  Next Obligation.
  Proof with auto.
    transitivity x...
    transitivity x0...
  Qed.

(** Dually... *)

Program Instance [ Transitive A R ] =>
  trans_co_contra_inv_impl_morphism : Morphism (R ++> R --> inverse impl) R.
  
  Next Obligation.
  Proof with auto.
    apply* trans_contra_co_morphism ; eauto. eauto.
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

Program Instance [ Transitive A R ] (x : A) =>
  trans_contra_inv_impl_morphism : Morphism (R --> inverse impl) (R x).

  Next Obligation.
  Proof with auto.
    transitivity y...
  Qed.

Program Instance [ Transitive A R ] (x : A) =>
  trans_co_impl_morphism : Morphism (R ==> impl) (R x).

  Next Obligation.
  Proof with auto.
    transitivity x0...
  Qed.

Program Instance [ Transitive A R, Symmetric A R ] (x : A) =>
  trans_sym_co_inv_impl_morphism : Morphism (R ==> inverse impl) (R x).

  Next Obligation.
  Proof with auto.
    transitivity y...
  Qed.

Program Instance [ Transitive A R, Symmetric _ R ] (x : A) =>
  trans_sym_contra_impl_morphism : Morphism (R --> impl) (R x).

  Next Obligation.
  Proof with auto.
    transitivity x0...
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

(** With Symmetric relations, variance is no issue ! *)

(* Program Instance (A B : Type) (R : relation A) (R' : relation B) *)
(*   [ Morphism _ (R ==> R') m ] [ Symmetric A R ] =>  *)
(*   sym_contra_morphism : Morphism (R --> R') m. *)

(*   Next Obligation. *)
(*   Proof with auto. *)
(*     repeat (red ; intros). apply respect. *)
(*     sym... *)
(*   Qed. *)

(** [R] is Reflexive, hence we can build the needed proof. *)

Program Instance [ Morphism (A -> B) (R ==> R') m, Reflexive _ R ] (x : A) =>
  Reflexive_partial_app_morphism : Morphism R' (m x) | 3.

(** Every Transitive relation induces a morphism by "pushing" an [R x y] on the left of an [R x z] proof
   to get an [R y z] goal. *)

Program Instance [ Transitive A R ] => 
  trans_co_eq_inv_impl_morphism : Morphism (R ==> (@eq A) ==> inverse impl) R.

  Next Obligation.
  Proof with auto.
    transitivity y...
  Qed.

Program Instance [ Transitive A R ] => 
  trans_contra_eq_impl_morphism : Morphism (R --> (@eq A) ==> impl) R.

  Next Obligation.
  Proof with auto.
    transitivity x...
  Qed.

(** Every Symmetric and Transitive relation gives rise to an equivariant morphism. *)

Program Instance [ Transitive A R, Symmetric _ R ] => 
  trans_sym_morphism : Morphism (R ==> R ==> iff) R.

  Next Obligation.
  Proof with auto.
    split ; intros.
    transitivity x0... transitivity x...
  
    transitivity y... transitivity y0... 
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

Instance (A : Type) [ Reflexive B R ] (m : A -> B) =>
  eq_reflexive_morphism : Morphism (@Logic.eq A ==> R) m | 3.
Proof. simpl_relation. Qed.

Instance (A : Type) [ Reflexive B R' ] => 
  Reflexive (@Logic.eq A ==> R').
Proof. simpl_relation. Qed.

Instance [ Morphism (A -> B) (inverse R ==> R') m ] =>
  Morphism (R ==> inverse R') m | 10.
Proof. firstorder. Qed.

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
  inverse (R ==> R') <R> (inverse R ==> inverse R').
Proof.
  intros.
  unfold flip, respectful.
  split ; intros ; intuition.
Qed.

Class (A : Type) (R : relation A) => Normalizes (m : A) (m' : A) : Prop :=
  normalizes : R m m'.

Instance (A : Type) (R : relation A) (B : Type) (R' : relation B) =>
  Normalizes relation_equivalence (inverse R ==> inverse R') (inverse (R ==> R')) .
Proof.
  reduce.
  symmetry ; apply inverse_respectful.
Qed.

Instance [ Normalizes (relation B) relation_equivalence R' (inverse R'') ] =>
  ! Normalizes (relation (A -> B)) relation_equivalence (inverse R ==> R') (inverse (R ==> R'')) .
Proof.
  red.
  pose normalizes.
  setoid_rewrite r.
  setoid_rewrite inverse_respectful.
  reflexivity.
Qed.

Program Instance [ Morphism A R m ] => 
  morphism_inverse_morphism : Morphism (inverse R) m | 2.

(** Bootstrap !!! *)

Instance morphism_morphism : Morphism (relation_equivalence ==> @eq _ ==> iff) (@Morphism A).
Proof.
  simpl_relation. 
  unfold relation_equivalence in H.
  split ; red ; intros.
  setoid_rewrite <- H.
  apply respect.
  setoid_rewrite H.
  apply respect.
Qed.
  
Lemma morphism_releq_morphism 
  [ Normalizes (relation A) relation_equivalence R R',
    Morphism _ R' m ] : Morphism R m.
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

(** Morphisms for relations *)

Instance [ PartialOrder A eqA R ] => 
   partial_order_morphism : Morphism (eqA ==> eqA ==> iff) R.
Proof with auto.
  intros. rewrite partial_order_equivalence.
  simpl_relation. firstorder.
    transitivity x... transitivity x0... 
    transitivity y... transitivity y0...
Qed.

Instance Morphism (relation_equivalence (A:=A) ==> 
  relation_equivalence ==> relation_equivalence) relation_conjunction.
  Proof. firstorder. Qed.

Instance Morphism (relation_equivalence (A:=A) ==> 
  relation_equivalence ==> relation_equivalence) relation_disjunction.
  Proof. firstorder. Qed.


(** Morphisms for quantifiers *)

Program Instance {A : Type} => ex_iff_morphism : Morphism (pointwise_relation iff ==> iff) (@ex A).

  Next Obligation.
  Proof.
    unfold pointwise_relation in H.     
    split ; intros.
    destruct H0 as [x₁ H₁].
    exists x₁. rewrite H in H₁. assumption.
    
    destruct H0 as [x₁ H₁].
    exists x₁. rewrite H. assumption.
  Qed.

Program Instance {A : Type} => ex_impl_morphism :
  Morphism (pointwise_relation impl ==> impl) (@ex A).

  Next Obligation.
  Proof.
    unfold pointwise_relation in H.  
    exists H0. apply H. assumption.
  Qed.

Program Instance {A : Type} => ex_inverse_impl_morphism : 
  Morphism (pointwise_relation (inverse impl) ==> inverse impl) (@ex A).

  Next Obligation.
  Proof.
    unfold pointwise_relation in H.  
    exists H0. apply H. assumption.
  Qed.

Program Instance {A : Type} => all_iff_morphism : 
  Morphism (pointwise_relation iff ==> iff) (@all A).

  Next Obligation.
  Proof.
    unfold pointwise_relation, all in *.
    intuition ; specialize (H x0) ; intuition.
  Qed.

Program Instance {A : Type} => all_impl_morphism : 
  Morphism (pointwise_relation impl ==> impl) (@all A).
  
  Next Obligation.
  Proof.
    unfold pointwise_relation, all in *.
    intuition ; specialize (H x0) ; intuition.
  Qed.

Program Instance {A : Type} => all_inverse_impl_morphism : 
  Morphism (pointwise_relation (inverse impl) ==> inverse impl) (@all A).
  
  Next Obligation.
  Proof.
    unfold pointwise_relation, all in *.
    intuition ; specialize (H x0) ; intuition.
  Qed.

Lemma inverse_pointwise_relation A (R : relation A) : 
  pointwise_relation (inverse R) <R> inverse (pointwise_relation (A:=A) R).
Proof. reflexivity. Qed.
