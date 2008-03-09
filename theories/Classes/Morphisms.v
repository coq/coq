(* -*- coq-prog-args: ("-emacs-U" "-nois") -*- *)
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

Require Import Coq.Program.Program.
Require Export Coq.Classes.Relations.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Morphisms.

   We now turn to the definition of [Morphism] and declare standard instances. 
   These will be used by the [clrewrite] tactic later. *)

(** Respectful morphisms. *)

Definition respectful_dep (A : Type) (R : relation A) 
  (B : A -> Type) (R' : forall x y, B x -> B y -> Prop) : relation (forall x : A, B x) := 
  fun f g => forall x y : A, R x y -> R' x y (f x) (g y).

Definition respectful A (R : relation A) B (R' : relation B) : relation (A -> B) :=
  fun f g => forall x y : A, R x y -> R' (f x) (g y).

(** Notations reminiscent of the old syntax for declaring morphisms. *)

Notation " R ++> R' " := (@respectful _ R _ R') (right associativity, at level 20).
Notation " R ==> R' " := (@respectful _ R _ R') (right associativity, at level 20).
Notation " R --> R' " := (@respectful _ (inverse R) _ R') (right associativity, at level 20).

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
  (fun (f g : respecting) => forall (x y : A), R x y -> R' (`f x) (`g y)).

  Next Obligation.
  Proof.
    constructor ; intros.
    destruct x ; simpl.
    apply r ; auto.
  Qed.

  Next Obligation.
  Proof.
    constructor ; intros.
    sym ; apply H.
    sym ; auto.
  Qed.

  Next Obligation.
  Proof.
    constructor ; intros.
    trans ((`y) y0).
    apply H ; auto.
    apply H0. refl.
  Qed.

(** Can't use the definition [notT] as it gives a universe inconsistency. *)

Ltac obligations_tactic ::= program_simpl ; simpl_relation.

Program Instance not_impl_morphism :
  Morphism (Prop -> Prop) (impl --> impl) not.

Program Instance not_iff_morphism : 
  Morphism (Prop -> Prop) (iff ++> iff) not.

(** We make the type implicit, it can be infered from the relations. *)

Implicit Arguments Morphism [A].

(** Leibniz *)

Program Definition eq_morphism A : Morphism (eq ++> eq ++> iff) (eq (A:=A)).
Proof. intros ; constructor ; intros.
  obligations_tactic.
  subst.
  intuition.
Qed.

(* Program Definition arrow_morphism `A B` (m : A -> B) : Morphism (eq ++> eq) m. *)

(** Any morphism respecting some relations up to [iff] respects 
   them up to [impl] in each way. Very important instances as we need [impl]
   morphisms at the top level when we rewrite. *)

Class SubRelation A (R S : relation A) :=
  subrelation :> Morphism (S ==> R) (fun x => x).

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
  constructor ; repeat red ; intros.
  destruct subrelation.
  red in respect0, H ; unfold id in *.
  apply respect0.
  apply H.
  apply H0.
Qed.

(** High priority because it is always applicable and loops. *)

Instance [ SubRelation A R₁ R₂, Morphism R₂ m ] =>
  subrelation_morphism : Morphism R₁ m | 4.
Proof.
  destruct subrelation.
  red in respect0.
  unfold id in * ; apply respect0.
  apply respect.
Qed.

(* Program Instance `A` (R : relation A) `B` (R' : relation B) *)
(*   [ ? Morphism (R ==> R' ==> iff) m ] => *)
(*   iff_impl_binary_morphism : ? Morphism (R ==> R' ==> impl) m. *)

(*   Next Obligation. *)
(*   Proof. *)
(*     destruct respect with x y x0 y0 ; auto. *)
(*   Qed. *)

(* Program Instance `A` (R : relation A) `B` (R' : relation B) *)
(*   [ ? Morphism (R ==> R' ==> iff) m ] => *)
(*   iff_inverse_impl_binary_morphism : ? Morphism (R ==> R' ==> inverse impl) m. *)

(*   Next Obligation. *)
(*   Proof. *)
(*     destruct respect with x y x0 y0 ; auto. *)
(*   Qed. *)


(* Program Instance [ Morphism (A -> Prop) (R ==> iff) m ] => *)
(*   iff_impl_morphism : ? Morphism (R ==> impl) m. *)

(*   Next Obligation. *)
(*   Proof. *)
(*     destruct respect with x y ; auto. *)
(*   Qed. *)

(* Program Instance [ Morphism (A -> Prop) (R ==> iff) m ] => *)
(*   iff_inverse_impl_morphism : ? Morphism (R ==> inverse impl) m. *)

(*   Next Obligation. *)
(*   Proof. *)
(*     destruct respect with x y ; auto. *)
(*   Qed. *)

(** Logical implication [impl] is a morphism for logical equivalence. *)

Program Instance iff_iff_iff_impl_morphism : Morphism (iff ==> iff ==> iff) impl.

Lemma reflexive_impl_iff [ ! Symmetric A R, Morphism (R ==> impl) m ] : Morphism (R ==> iff) m.
Proof.
  intros.
  constructor. red ; intros. 
  split ; apply respect ; [ idtac | sym ] ; auto.
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
    unfold flip. 
    apply respect ; auto.
  Qed.

(** Partial applications are ok when a proof of refl is available. *)

(** A proof of [R x x] is available. *)

(* Program Instance (A : Type) R B (R' : relation B) *)
(*   [ Morphism (R ==> R') m ] [ Morphism R x ] => *)
(*   morphism_partial_app_morphism : Morphism R' (m x). *)

(*   Next Obligation. *)
(*   Proof with auto. *)
(*     apply (respect (m:=m))... *)
(*     apply respect. *)
(*   Qed. *)

(** Every morphism gives rise to a morphism on the inverse relation. *)

Program Instance (A : Type) (R : relation A) (B : Type) (R' : relation B)
  [ Morphism (R ==> R') m ] => morphism_inverse_morphism :
  Morphism (inverse R ==> inverse R') m.

  Next Obligation.
  Proof.
    unfold inverse in *.
    pose respect.
    unfold respectful in r.
    apply r ; auto.
  Qed.

(** Morphism declarations for partial applications. *)

Program Instance [ ! Transitive A R ] (x : A) =>
  trans_contra_inv_impl_morphism : Morphism (R --> inverse impl) (R x).

  Next Obligation.
  Proof with auto.
    trans y...
  Qed.

Program Instance [ ! Transitive A R ] (x : A) =>
  trans_co_impl_morphism : Morphism (R ==> impl) (R x).

  Next Obligation.
  Proof with auto.
    trans x0...
  Qed.

Program Instance [ ! Transitive A R, Symmetric R ] (x : A) =>
  trans_sym_co_inv_impl_morphism : Morphism (R ==> inverse impl) (R x).

  Next Obligation.
  Proof with auto.
    trans y...
    sym...
  Qed.

Program Instance [ ! Transitive A R, Symmetric R ] (x : A) =>
  trans_sym_contra_impl_morphism : Morphism (R --> impl) (R x).

  Next Obligation.
  Proof with auto.
    trans x0...
    sym...
  Qed.

Program Instance [ Equivalence A R ] (x : A) =>
  equivalence_partial_app_morphism : Morphism (R ==> iff) (R x).

  Next Obligation.
  Proof with auto.
    split. intros ; trans x0...
    intros.
    trans y...
    sym...
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
    refl.
  Qed.

(** Every transitive relation induces a morphism by "pushing" an [R x y] on the left of an [R x z] proof
   to get an [R y z] goal. *)

Program Instance [ ! Transitive A R ] => 
  trans_co_eq_inv_impl_morphism : Morphism (R ==> eq ==> inverse impl) R.

  Next Obligation.
  Proof with auto.
    trans y...
    subst x0...
  Qed.

Program Instance [ ! Transitive A R ] => 
  trans_contra_eq_impl_morphism : Morphism (R --> eq ==> impl) R.

  Next Obligation.
  Proof with auto.
    trans x...
    subst x0...
  Qed.

(** Every symmetric and transitive relation gives rise to an equivariant morphism. *)

Program Instance [ ! Transitive A R, Symmetric R ] => 
  trans_sym_morphism : Morphism (R ==> R ==> iff) R.

  Next Obligation.
  Proof with auto.
    split ; intros.
    trans x0... trans x... sym...
  
    trans y... trans y0... sym...
  Qed.

Program Instance [ Equivalence A R ] => 
  equiv_morphism : Morphism (R ==> R ==> iff) R.

  Next Obligation.
  Proof with auto.
    split ; intros.
    trans x0... trans x... sym...
  
    trans y... trans y0... sym...
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

Instance {A B : Type} (m : A -> B) =>
  any_eq_eq_morphism : Morphism (@Logic.eq A ==> @Logic.eq B) m | 4.
Proof.
  red ; intros. subst ; reflexivity.
Qed.

Instance {A : Type} (m : A -> Prop) =>
  any_eq_iff_morphism : Morphism (@Logic.eq A ==> iff) m | 4.
Proof.
  red ; intros. subst ; split; trivial.
Qed.
