(* -*- coq-prog-args: ("-emacs-U" "-nois") -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Typeclass-based setoids, tactics and standard instances.
 
   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
   91405 Orsay, France *)

(* $Id$ *)

Require Export Coq.Program.Basics.
Require Import Coq.Program.Tactics.

Require Import Coq.Classes.Init.
Require Import Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.

Open Local Scope signature_scope.

(** Every [Equivalence] gives a default relation, if no other is given (lowest priority). *)

Instance [ Equivalence A R ] => 
  equivalence_default : DefaultRelation A R | 4.

Definition equiv [ Equivalence A R ] : relation A := R.

Typeclasses unfold @equiv.

(* (** Shortcuts to make proof search possible (unification won't unfold equiv). *) *)

(* Program Instance [ sa : Equivalence A ] => equiv_refl : Reflexive equiv. *)

(* Program Instance [ sa : Equivalence A ] => equiv_sym : Symmetric equiv. *)

(*   Next Obligation. *)
(*   Proof. *)
(*     symmetry ; auto. *)
(*   Qed. *)

(* Program Instance [ sa : Equivalence A ] => equiv_trans : Transitive equiv. *)

(*   Next Obligation. *)
(*   Proof. *)
(*     transitivity y ; auto. *)
(*   Qed. *)

(** Overloaded notations for setoid equivalence and inequivalence. Not to be confused with [eq] and [=]. *)

(** Subset objects should be first coerced to their underlying type, but that notation doesn't work in the standard case then. *)
(* Notation " x == y " := (equiv (x :>) (y :>)) (at level 70, no associativity) : type_scope. *)

Notation " x === y " := (equiv x y) (at level 70, no associativity) : equiv_scope.

Notation " x =/= y " := (complement equiv x y) (at level 70, no associativity) : equiv_scope.
  
Open Local Scope equiv_scope.

Lemma nequiv_equiv_trans : forall [ Equivalence A ] (x y z : A), x =/= y -> y === z -> x =/= z.
Proof with auto.
  intros; intro.
  assert(z === y) by (symmetry ; auto).
  assert(x === y) by (transitivity z ; auto).
  contradiction.
Qed.

Lemma equiv_nequiv_trans : forall [ Equivalence A ] (x y z : A), x === y -> y =/= z -> x =/= z.
Proof.
  intros; intro. 
  assert(y === x) by (symmetry ; auto).
  assert(y === z) by (transitivity x ; auto).
  contradiction.
Qed.

(** Use the [substitute] command which substitutes an applied relation in every hypothesis. *)

Ltac setoid_subst H := 
  match type of H with
    ?x === ?y => substitute H ; clear H x
  end.

Ltac setoid_subst_nofail :=
  match goal with
    | [ H : ?x === ?y |- _ ] => setoid_subst H ; setoid_subst_nofail
    | _ => idtac
  end.
  
(** [subst*] will try its best at substituting every equality in the goal. *)

Tactic Notation "subst" "*" := subst_no_fail ; setoid_subst_nofail.

Ltac equiv_simplify_one :=
  match goal with
    | [ H : ?x === ?x |- _ ] => clear H
    | [ H : ?x === ?y |- _ ] => setoid_subst H
    | [ |- ?x =/= ?y ] => let name:=fresh "Hneq" in intro name
    | [ |- ~ ?x === ?y ] => let name:=fresh "Hneq" in intro name
  end.

Ltac equiv_simplify := repeat equiv_simplify_one.

Ltac equivify_tac :=
  match goal with
    | [ s : Equivalence ?A ?R, H : ?R ?x ?y |- _ ] => change R with (@equiv A R s) in H
    | [ s : Equivalence ?A ?R |- context C [ ?R ?x ?y ] ] => change (R x y) with (@equiv A R s x y)
  end.

Ltac equivify := repeat equivify_tac.

(** Every equivalence relation gives rise to a morphism, as it is Transitive and Symmetric. *)

(* Instance [ sa : Equivalence ] => equiv_morphism : Morphism (equiv ++> equiv ++> iff) equiv := *)
(*   respect := respect. *)

(* (** The partial application too as it is Reflexive. *) *)

(* Instance [ sa : Equivalence A ] (x : A) =>  *)
(*   equiv_partial_app_morphism : Morphism (equiv ++> iff) (equiv x) := *)
(*   respect := respect.  *)

(** Instance not exported by default, as comparing types for equivalence may be unintentional. *)

Section Type_Equivalence.

  Definition type_eq : relation Type :=
    fun x y => x = y.
  
  Program Instance type_equivalence : Equivalence Type type_eq.
  
  Next Obligation. 
  Proof. unfold type_eq in *. subst. reflexivity. Qed.

End Type_Equivalence.

(** Partial equivs don't require reflexivity so we can build a partial equiv on the function space. *)

Class PartialEquivalence (carrier : Type) (pequiv : relation carrier) :=
  pequiv_prf :> PER carrier pequiv.

Definition pequiv [ PartialEquivalence A R ] : relation A := R.
Typeclasses unfold @pequiv.

(** Overloaded notation for partial equiv equivalence. *)

Notation " x =~= y " := (pequiv x y) (at level 70, no associativity) : type_scope.

Section Respecting.

  (** Here we build an equivalence instance for functions which relates respectful ones only, 
     we do not export it. *)

  Definition respecting [ Equivalence A (R : relation A), Equivalence B (R' : relation B) ] : Type := 
    { morph : A -> B | respectful R R' morph morph }.
  
  Program Instance [ Equivalence A R, Equivalence B R' ] => 
    respecting_equiv : Equivalence respecting
    (fun (f g : respecting) => forall (x y : A), R x y -> R' (proj1_sig f x) (proj1_sig g y)).

  Solve Obligations using unfold respecting in * ; simpl_relation ; program_simpl.

  Next Obligation.
  Proof. 
    unfold respecting in *. program_simpl. red in H2,H3,H4. 
    transitivity (y x0) ; auto.
    transitivity (y y0) ; auto.
    symmetry. auto.
  Qed.

End Respecting.