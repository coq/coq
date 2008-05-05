(* -*- coq-prog-args: ("-emacs-U" "-top" "Coq.Classes.Morphisms"); compile-command: "make -C ../.. TIME='time'" -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Typeclass-based morphism definition and standard, minimal instances.
 
   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
   91405 Orsay, France *)

(* $Id$ *)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Morphisms.

   We now turn to the definition of [Morphism] and declare standard instances. 
   These will be used by the [setoid_rewrite] tactic later. *)

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

Definition respectful (A B : Type) 
  (R : relation A) (R' : relation B) : relation (A -> B) :=
  Eval compute in @respectful_hetero A A (fun _ => B) (fun _ => B) R (fun _ _ => R').

(** Notations reminiscent of the old syntax for declaring morphisms. *)

Delimit Scope signature_scope with signature.

Notation " R ++> R' " := (@respectful _ _ (R%signature) (R'%signature)) 
  (right associativity, at level 90) : signature_scope.

Notation " R ==> R' " := (@respectful _ _ (R%signature) (R'%signature))
  (right associativity, at level 90) : signature_scope.

Notation " R --> R' " := (@respectful _ _ (inverse (R%signature)) (R'%signature))
  (right associativity, at level 90) : signature_scope.

Arguments Scope respectful [type_scope type_scope signature_scope signature_scope].

Open Local Scope signature_scope.

(** A morphism on a relation [R] is an object respecting the relation (in its kernel). 
   The relation [R] will be instantiated by [respectful] and [A] by an arrow type 
   for usual morphisms. *)

Class Morphism A (R : relation A) (m : A) : Prop :=
  respect : R m m.

Arguments Scope Morphism [type_scope signature_scope].

(** We make the type implicit, it can be infered from the relations. *)

Implicit Arguments Morphism [A].

(** We allow to unfold the [relation] definition while doing morphism search. *)

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

Lemma subrelation_morphism [ sub : subrelation A R₁ R₂, mor : Morphism A R₁ m ] : Morphism R₂ m.
Proof.
  intros. apply sub. apply mor.
Qed.

Instance morphism_subrelation_morphism : 
  Morphism (subrelation ++> @eq _ ==> impl) (@Morphism A).
Proof. reduce. subst. firstorder. Qed.

(** We use an external tactic to manage the application of subrelation, which is otherwise
   always applicable. We allow its use only once per branch. *)

Inductive subrelation_done : Prop :=
  did_subrelation : subrelation_done.

Ltac subrelation_tac := 
  match goal with
    | [ _ : subrelation_done |- _ ] => fail 1
    | [ |- @Morphism _ _ _ ] => let H := fresh "H" in
      set(H:=did_subrelation) ; eapply @subrelation_morphism
  end.

Hint Extern 4 (@Morphism _ _ _) => subrelation_tac : typeclass_instances.

(** Essential subrelation instances for [iff], [impl] and [pointwise_relation]. *)

Instance iff_impl_subrelation : subrelation iff impl.
Proof. firstorder. Qed.

Instance iff_inverse_impl_subrelation : subrelation iff (inverse impl).
Proof. firstorder. Qed.

Instance [ sub : subrelation A R R' ] => pointwise_subrelation :
  subrelation (pointwise_relation (A:=B) R) (pointwise_relation R') | 4.
Proof. reduce. unfold pointwise_relation in *. apply sub. apply H. Qed.

(** The complement of a relation conserves its morphisms. *)

Program Instance [ mR : Morphism (A -> A -> Prop)
  (RA ==> RA ==> iff) R ] => 
  complement_morphism : Morphism (RA ==> RA ==> iff)
  (complement R).

  Next Obligation.
  Proof.
    unfold complement.
    pose (mR x y H x0 y0 H0).
    intuition.
  Qed.

(** The [inverse] too, actually the [flip] instance is a bit more general. *) 

Program Instance [ mor : Morphism (A -> B -> C) (RA ==> RB ==> RC) f ] => 
  flip_morphism : Morphism (RB ==> RA ==> RC) (flip f).

  Next Obligation.
  Proof.
    apply mor ; auto.
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

(* (** Dually... *) *)

(* Program Instance [ Transitive A R ] => *)
(*   trans_co_contra_inv_impl_morphism : Morphism (R ++> R --> inverse impl) R. *)
  
(*   Next Obligation. *)
(*   Proof with auto. *)
(*     apply* trans_contra_co_morphism ; eauto. eauto. *)
(*   Qed. *)

(** Morphism declarations for partial applications. *)

Program Instance [ Transitive A R ] =>
  trans_contra_inv_impl_morphism : Morphism (R --> inverse impl) (R x).

  Next Obligation.
  Proof with auto.
    transitivity y...
  Qed.

Program Instance [ Transitive A R ] =>
  trans_co_impl_morphism : Morphism (R ==> impl) (R x).

  Next Obligation.
  Proof with auto.
    transitivity x0...
  Qed.

Program Instance [ Transitive A R, Symmetric A R ] =>
  trans_sym_co_inv_impl_morphism : Morphism (R ==> inverse impl) (R x).

  Next Obligation.
  Proof with auto.
    transitivity y...
  Qed.

Program Instance [ Transitive A R, Symmetric _ R ] =>
  trans_sym_contra_impl_morphism : Morphism (R --> impl) (R x).

  Next Obligation.
  Proof with auto.
    transitivity x0...
  Qed.

Program Instance [ Equivalence A R ] =>
  equivalence_partial_app_morphism : Morphism (R ==> iff) (R x).

  Next Obligation.
  Proof with auto.
    split. intros ; transitivity x0...
    intros.
    transitivity y...
    symmetry...
  Qed.

(** Every Transitive relation induces a morphism by "pushing" an [R x y] on the left of an [R x z] proof
   to get an [R y z] goal. *)

Program Instance [ Transitive A R ] => 
  trans_co_eq_inv_impl_morphism : Morphism (R ==> (@eq A) ==> inverse impl) R.

  Next Obligation.
  Proof with auto.
    transitivity y...
  Qed.

(* Program Instance [ Transitive A R ] =>  *)
(*   trans_contra_eq_impl_morphism : Morphism (R --> (@eq A) ==> impl) R. *)

(*   Next Obligation. *)
(*   Proof with auto. *)
(*     transitivity x... *)
(*   Qed. *)

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
  
(** Coq functions are morphisms for leibniz equality, 
   applied only if really needed. *)

(* Instance (A : Type) [ Reflexive B R ] => *)
(*   eq_reflexive_morphism : Morphism (@Logic.eq A ==> R) m | 3. *)
(* Proof. simpl_relation. Qed. *)

Instance (A : Type) [ Reflexive B R' ] =>
  Reflexive (@Logic.eq A ==> R').
Proof. simpl_relation. Qed.

(** [respectful] is a morphism for relation equivalence. *)

Instance respectful_morphism : 
  Morphism (relation_equivalence ++> relation_equivalence ++> relation_equivalence) (@respectful A B).
Proof.
  reduce.
  unfold respectful, relation_equivalence, predicate_equivalence in * ; simpl in *.
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

(** Every element in the carrier of a reflexive relation is a morphism for this relation.
   We use a proxy class for this case which is used internally to discharge reflexivity constraints.
   The [Reflexive] instance will almost always be used, but it won't apply in general to any kind of 
   [Morphism (A -> B) _ _] goal, making proof-search much slower. A cleaner solution would be to be able
   to set different priorities in different hint bases and select a particular hint database for
   resolution of a type class constraint.*) 

Class MorphismProxy A (R : relation A) (m : A) : Prop :=
  respect_proxy : R m m.

Instance [ Reflexive A R ] (x : A) => 
  reflexive_morphism_proxy : MorphismProxy A R x | 1.
Proof. firstorder. Qed.

Instance [ Morphism A R x ] =>
  morphism_morphism_proxy : MorphismProxy A R x | 2.
Proof. firstorder. Qed.

(* Instance (A : Type) [ Reflexive B R ] => *)
(*   eq_reflexive_morphism : Morphism (@Logic.eq A ==> R) m | 3. *)
(* Proof. simpl_relation. Qed. *)

(** [R] is Reflexive, hence we can build the needed proof. *)

Lemma Reflexive_partial_app_morphism [ Morphism (A -> B) (R ==> R') m, Reflexive A R ] (x : A) :
   Morphism R' (m x).
Proof. simpl_relation. Qed.

Ltac partial_application_tactic := 
  let tac x :=
    match type of x with
      | Type => fail 1
      | _ => eapply @Reflexive_partial_app_morphism
    end
  in
  let on_morphism m :=
    match m with
      | ?m' ?x => tac x
      | ?m' _ ?x => tac x
      | ?m' _ _ ?x => tac x
      | ?m' _ _ _ ?x => tac x
      | ?m' _ _ _ _ ?x => tac x
      | ?m' _ _ _ _ _ ?x => tac x
      | ?m' _ _ _ _ _ _ ?x => tac x
      | ?m' _ _ _ _ _ _ _ ?x => tac x
      | ?m' _ _ _ _ _ _ _ _ ?x => tac x
    end
  in
  match goal with
    | [ |- @Morphism _ _ ?m ] => on_morphism m
  end.

(* Program Instance [ Morphism (A -> B) (R ==> R') m, Reflexive A R ] (x : A) => *)
(*   reflexive_partial_app_morphism : Morphism R' (m x). *)

Hint Extern 4 (@Morphism _ _ _) => partial_application_tactic : typeclass_instances.

Lemma inverse_respectful : forall (A : Type) (R : relation A) (B : Type) (R' : relation B),
  relation_equivalence (inverse (R ==> R')) (inverse R ==> inverse R').
Proof.
  intros.
  unfold flip, respectful.
  split ; intros ; intuition.
Qed.

(** Special-purpose class to do normalization of signatures w.r.t. inverse. *)

Class (A : Type) => Normalizes (m : relation A) (m' : relation A) : Prop :=
  normalizes : relation_equivalence m m'.

Instance inverse_respectful_norm : 
  Normalizes (A -> B) (inverse R ==> inverse R') (inverse (R ==> R')) .
Proof. firstorder. Qed.

(* If not an inverse on the left, do a double inverse. *)

Instance not_inverse_respectful_norm : 
  Normalizes (A -> B) (R ==> inverse R') (inverse (inverse R ==> R')) | 4.
Proof. firstorder. Qed.

Instance [ Normalizes B R' (inverse R'') ] =>
  inverse_respectful_rec_norm : Normalizes (A -> B) (inverse R ==> R') (inverse (R ==> R'')).
Proof. red ; intros.  
  pose normalizes as r.
  setoid_rewrite r.
  setoid_rewrite inverse_respectful.
  reflexivity.
Qed.

(** Once we have normalized, we will apply this instance to simplify the problem. *)

Program Instance [ Morphism A R m ] => 
  morphism_inverse_morphism : Morphism (inverse R) m | 2.

(** Bootstrap !!! *)

Instance morphism_morphism : Morphism (relation_equivalence ==> @eq _ ==> iff) (@Morphism A).
Proof.
  simpl_relation.
  reduce in H.
  split ; red ; intros.
  setoid_rewrite <- H.
  apply H0.
  setoid_rewrite H.
  apply H0.
Qed.

Lemma morphism_releq_morphism [ Normalizes A R R', Morphism _ R' m ] : Morphism R m.
Proof.
  intros.
  pose respect as r.
  pose normalizes as norm.
  setoid_rewrite norm.
  assumption.
Qed.

Inductive normalization_done : Prop := did_normalization.

Ltac morphism_normalization := 
  match goal with
    | [ _ : normalization_done |- _ ] => fail 1
    | [ |- @Morphism _ _ _ ] => let H := fresh "H" in
      set(H:=did_normalization) ; eapply @morphism_releq_morphism
  end.

Hint Extern 6 (@Morphism _ _ _) => morphism_normalization : typeclass_instances.

(** Every reflexive relation gives rise to a morphism, only for immediately solving goals without variables. *)

Lemma reflexive_morphism [ Reflexive A R ] (x : A)
   : Morphism R x.
Proof. firstorder. Qed.

Ltac morphism_reflexive :=
  match goal with
    | [ _ : normalization_done |- _ ] => fail 1
    | [ _ : subrelation_done |- _ ] => fail 1
    | [ |- @Morphism _ _ _ ] => eapply @reflexive_morphism
  end.

Hint Extern 4 (@Morphism _ _ _) => morphism_reflexive : typeclass_instances.