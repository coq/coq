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
Require Import Coq.Classes.Init.
Require Export Coq.Classes.Relations.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Morphisms.

   We now turn to the definition of [Morphism] and declare standard instances. 
   These will be used by the [clrewrite] tactic later. *)

(** Respectful morphisms. *)

Definition respectful_depT (A : Type) (R : relationT A) 
  (B : A -> Type) (R' : forall x y, B x -> B y -> Type) : relationT (forall x : A, B x) := 
  fun f g => forall x y : A, R x y -> R' x y (f x) (g y).

Definition respectfulT A (eqa : relationT A) B (eqb : relationT B) : relationT (A -> B) :=
  Eval compute in (respectful_depT eqa (fun _ _ => eqb)).

Definition respectful A (R : relation A) B (R' : relation B) : relation (A -> B) :=
  fun f g => forall x y : A, R x y -> R' (f x) (g y).

(** Notations reminiscent of the old syntax for declaring morphisms.
   We use three + or - for type morphisms, and two for [Prop] ones.
   *)

Notation " R +++> R' " := (@respectfulT _ R _ R') (right associativity, at level 20).
Notation " R ---> R' " := (@respectfulT _ (flip R) _ R') (right associativity, at level 20).

Notation " R ++> R' " := (@respectful _ R _ R') (right associativity, at level 20).
Notation " R --> R' " := (@respectful _ (inverse R) _ R') (right associativity, at level 20).

(** A morphism on a relation [R] is an object respecting the relation (in its kernel). 
   The relation [R] will be instantiated by [respectful] and [A] by an arrow type 
   for usual morphisms. *)

Class Morphism A (R : relationT A) (m : A) :=
  respect : R m m.

(** Here we build an equivalence instance for functions which relates respectful ones only. *)

Definition respecting [ Equivalence A (R : relation A), Equivalence B (R' : relation B) ] : Type := 
  { morph : A -> B | respectful R R' morph morph }.

Ltac obligations_tactic ::= program_simpl.

Program Instance [ Equivalence A (R : relation A), Equivalence B (R' : relation B) ] => 
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

Program Instance notT_arrow_morphism : 
  Morphism (Type -> Type) (arrow ---> arrow) (fun X : Type => X -> False).

Program Instance not_iso_morphism : 
  Morphism (Type -> Type) (iso +++> iso) (fun X : Type => X -> False).

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

(** Any binary morphism respecting some relations up to [iff] respects 
   them up to [impl] in each way. Very important instances as we need [impl]
   morphisms at the top level when we rewrite. *)

Program Instance `A` (R : relation A) `B` (R' : relation B)
  [ ? Morphism (R ++> R' ++> iff) m ] =>

  iff_impl_binary_morphism : ? Morphism (R ++> R' ++> impl) m.

  Next Obligation.
  Proof.
    destruct respect with x y x0 y0 ; auto.
  Qed.

Program Instance `A` (R : relation A) `B` (R' : relation B)
  [ ? Morphism (R ++> R' ++> iff) m ] =>
  iff_inverse_impl_binary_morphism : ? Morphism (R ++> R' ++> inverse impl) m.

  Next Obligation.
  Proof.
    destruct respect with x y x0 y0 ; auto.
  Qed.

(** The complement of a relation conserves its morphisms. *)

Program Instance `A` (RA : relation A) [ ? Morphism (RA ++> RA ++> iff) R ] => 
  complement_morphism : ? Morphism (RA ++> RA ++> iff) (complement R).

  Next Obligation.
  Proof.
    unfold complement ; intros.
    pose (respect).
    pose (r x y H).
    pose (r0 x0 y0 H0).
    intuition.
  Qed.

(** The inverse too. *)

Program Instance `A` (RA : relation A) [ ? Morphism (RA ++> RA ++> iff) R ] => 
  inverse_morphism : ? Morphism (RA ++> RA ++> iff) (inverse R).

  Next Obligation.
  Proof.
    unfold inverse ; unfold flip.
    apply respect ; auto.
  Qed.

(* Definition respectful' A (R : relation A) B (R' : relation B) (f : A -> B) : relation A := *)
(*   fun x y => R x y -> R' (f x) (f y). *)

(* Definition morphism_respectful' A (R : relation A) B (R' : relation B) (f : A -> B) *)
(*   [ ? Morphism (R ++> R') f ] (x y : A) : respectful' R R' f x y. *)
(* intros. *)
(* destruct H. *)
(* red in respect0. *)
(* red.  *)
(* apply respect0. *)
(* Qed. *)

(* Existing Instance morphism_respectful'. *)

(* Goal forall A [ Equivalence A (eqA : relation A) ] (R : relation A) [ ? Morphism (eqA ++> iff) m ] (x y : A)  *)
(*   [ ? Morphism (eqA ++> eqA) m' ] (m' : A -> A), eqA x y -> True. *)
(*   intros. *)
(*   cut (relation A) ; intros R'. *)
(*   cut ((eqA ++> R') m' m') ; intros. *)
(*   assert({ R' : relation A & Reflexive R' }). *)
(*   econstructor. *)
(*   typeclass_instantiation. *)
  

(*   assert (exists R' : relation A, Morphism ((fun x y => eqA x y -> R' (m' x) (m' y)) ++> iff) m). *)
(*   eapply ex_intro. *)
(*   unfold respectful. *)
(*   typeclass_instantiation. *)
  

(*   assert (exists R', Morphism (R' ++> iff) m /\ Morphism (eqA ++> R') m'). *)
(*   typeclass_instantiation. *)
(*   Set Printing All. *)
(*   Show Proof. *)
  
  
(*   apply respect. *)

(** Partial applications are ok when a proof of refl is available. *)

(** A proof of [R x x] is available. *)

(* Program Instance (A : Type) (R : relation A) B (R' : relation B) *)
(*   [ ? Morphism (R ++> R') m ] [ ? Morphism R x ] => *)
(*   morphism_partial_app_morphism : ? Morphism R' (m x). *)

(*   Next Obligation. *)
(*   Proof with auto. *)
(*     apply (respect (m:=m))... *)
(*     apply respect. *)
(*   Qed. *)


(** Morpshism declarations for partial applications. *)

Program Instance [ Transitive A (R : relation A) ] (x : A) =>
  trans_contra_inv_impl_morphism : ? Morphism (R --> inverse impl) (R x).

  Next Obligation.
  Proof with auto.
    trans y...
  Qed.

Program Instance [ Transitive A (R : relation A) ] (x : A) =>
  trans_co_impl_morphism : ? Morphism (R ++> impl) (R x).

  Next Obligation.
  Proof with auto.
    trans x0...
  Qed.

Program Instance [ Transitive A (R : relation A), Symmetric A R ] (x : A) =>
  trans_sym_co_inv_impl_morphism : ? Morphism (R ++> inverse impl) (R x).

  Next Obligation.
  Proof with auto.
    trans y...
    sym...
  Qed.

Program Instance [ Transitive A (R : relation A), Symmetric A R ] (x : A) =>
  trans_sym_contra_impl_morphism : ? Morphism (R --> impl) (R x).

  Next Obligation.
  Proof with auto.
    trans x0...
    sym...
  Qed.

Program Instance [ Equivalence A (R : relation A) ] (x : A) =>
  equivalence_partial_app_morphism : ? Morphism (R ++> iff) (R x).

  Next Obligation.
  Proof with auto.
    split. intros ; trans x0...
    intros.
    trans y...
    sym...
  Qed.

(** With symmetric relations, variance is no issue ! *)

Program Instance [ Symmetric A (R : relation A) ] B (R' : relation B) 
  [ Morphism _ (R ++> R') m ] => 
  sym_contra_morphism : ? Morphism (R --> R') m.

  Next Obligation.
  Proof with auto.
    repeat (red ; intros). apply respect.
    sym...
  Qed.

(** [R] is reflexive, hence we can build the needed proof. *)

Program Instance [ Reflexive A (R : relation A) ] B (R' : relation B)
  [ ? Morphism (R ++> R') m ] (x : A) =>
  reflexive_partial_app_morphism : ? Morphism R' (m x).

  Next Obligation.
  Proof with auto.
    intros.
    apply (respect (m:=m))...
    refl.
  Qed.

(** Every symmetric and transitive relation gives rise to an equivariant morphism. *)

Program Instance [ Transitive A (R : relation A), Symmetric A R ] => 
  trans_sym_morphism : ? Morphism (R ++> R ++> iff) R.

  Next Obligation.
  Proof with auto.
    split ; intros.
    trans x0... trans x... sym...
  
    trans y... trans y0... sym...
  Qed.

Program Instance [ Equivalence A (R : relation A) ] => 
  equiv_morphism : ? Morphism (R ++> R ++> iff) R.

  Next Obligation.
  Proof with auto.
    split ; intros.
    trans x0... trans x... sym...
  
    trans y... trans y0... sym...
  Qed.

(** In case the rewrite happens at top level. *)

Program Instance iff_inverse_impl_id : 
  ? Morphism (iff ++> inverse impl) id.

Program Instance inverse_iff_inverse_impl_id : 
  ? Morphism (iff --> inverse impl) id.
  
Program Instance iff_impl_id : 
  ? Morphism (iff ++> impl) id.

Program Instance inverse_iff_impl_id : 
  ? Morphism (iff --> impl) id.
  
(** Standard instances for [iff] and [impl]. *)

(** Logical conjunction. *)

(* Program Instance and_impl_iff_morphism : ? Morphism (impl ++> iff ++> impl) and. *)

(* Program Instance and_iff_impl_morphism : ? Morphism (iff ++> impl ++> impl) and. *)

Program Instance and_iff_morphism : ? Morphism (iff ++> iff ++> iff) and.

(** Logical disjunction. *)

(* Program Instance or_impl_iff_morphism : ? Morphism (impl ++> iff ++> impl) or. *)

(* Program Instance or_iff_impl_morphism : ? Morphism (iff ++> impl ++> impl) or. *)

Program Instance or_iff_morphism : ? Morphism (iff ++> iff ++> iff) or.
