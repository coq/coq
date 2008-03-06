(* -*- coq-prog-args: ("-emacs-U" "-nois") -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Typeclass-based setoids, tactics and standard instances.
   TODO: explain clrewrite, clsubstitute and so on.
 
   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
   91405 Orsay, France *)

(* $Id: FSetAVL_prog.v 616 2007-08-08 12:28:10Z msozeau $ *)

Require Export Coq.Program.Basics.
Require Import Coq.Program.Program.

Require Import Coq.Classes.Init.
Require Export Coq.Classes.Relations.
Require Export Coq.Classes.Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.

Definition equiv [ Equivalence A R ] : relation A := R.

(** Shortcuts to make proof search possible (unification won't unfold equiv). *)

Definition equivalence_refl [ sa : ! Equivalence A ] : Reflexive equiv.
Proof. eauto with typeclass_instances. Qed.

Definition equivalence_sym [ sa : ! Equivalence A ] : Symmetric equiv.
Proof. eauto with typeclass_instances. Qed.

Definition equivalence_trans [ sa : ! Equivalence A ] : Transitive equiv.
Proof. eauto with typeclass_instances. Qed.

(** Overloaded notations for setoid equivalence and inequivalence. Not to be confused with [eq] and [=]. *)

(** Subset objects should be first coerced to their underlying type, but that notation doesn't work in the standard case then. *)
(* Notation " x == y " := (equiv (x :>) (y :>)) (at level 70, no associativity) : type_scope. *)

Notation " x === y " := (equiv x y) (at level 70, no associativity) : equiv_scope.

Notation " x =/= y " := (complement equiv x y) (at level 70, no associativity) : equiv_scope.

Open Local Scope equiv_scope.

(** Use the [clsubstitute] command which substitutes an equality in every hypothesis. *)

Ltac clsubst H := 
  match type of H with
    ?x === ?y => clsubstitute H ; clear H x
  end.

Ltac clsubst_nofail :=
  match goal with
    | [ H : ?x === ?y |- _ ] => clsubst H ; clsubst_nofail
    | _ => idtac
  end.
  
(** [subst*] will try its best at substituting every equality in the goal. *)

Tactic Notation "clsubst" "*" := clsubst_nofail.

Ltac setoidreplace H t :=
  let Heq := fresh "Heq" in
    cut(H) ; [ intro Heq ; setoid_rewrite Heq ; clear Heq | unfold equiv ; t ].

Ltac setoidreplacein H H' t :=
  let Heq := fresh "Heq" in
    cut(H) ; [ intro Heq ; setoid_rewrite Heq in H' ; clear Heq | unfold equiv ; t ].

Tactic Notation "setoid_replace" constr(x) "with" constr(y) :=
  setoidreplace (x === y) idtac.

Tactic Notation "setoid_replace" constr(x) "with" constr(y) "in" hyp(id) :=
  setoidreplacein (x === y) id idtac.

Tactic Notation "setoid_replace" constr(x) "with" constr(y) "by" tactic(t) :=
  setoidreplace (x === y) ltac:t.

Tactic Notation "setoid_replace" constr(x) "with" constr(y) "in" hyp(id) "by" tactic(t) :=
  setoidreplacein (x === y) id ltac:t.

Tactic Notation "setoid_replace" constr(x) "with" constr(y) "using" "relation" constr(rel) :=
  setoidreplace (rel x y) idtac.

Tactic Notation "setoid_replace" constr(x) "with" constr(y) 
  "using" "relation" constr(rel) "by" tactic(t) :=
  setoidreplace (rel x y) ltac:t.

Tactic Notation "setoid_replace" constr(x) "with" constr(y) "in" hyp(id) 
  "using" "relation" constr(rel) :=
  setoidreplacein (rel x y) id idtac.

Tactic Notation "setoid_replace" constr(x) "with" constr(y) "in" hyp(id)
  "using" "relation" constr(rel) "by" tactic(t) :=
  setoidreplacein (rel x y) id ltac:t.
  
Lemma nequiv_equiv_trans : forall [ ! Equivalence A ] (x y z : A), x =/= y -> y === z -> x =/= z.
Proof with auto.
  intros; intro.
  assert(z === y) by relation_sym.
  assert(x === y) by relation_trans.
  contradiction.
Qed.

Lemma equiv_nequiv_trans : forall [ ! Equivalence A ] (x y z : A), x === y -> y =/= z -> x =/= z.
Proof.
  intros; intro. 
  assert(y === x) by relation_sym.
  assert(y === z) by relation_trans.
  contradiction.
Qed.

Ltac equiv_simplify_one :=
  match goal with
    | [ H : (?x === ?x)%type |- _ ] => clear H
    | [ H : (?x === ?y)%type |- _ ] => clsubst H
    | [ |- (?x =/= ?y)%type ] => let name:=fresh "Hneq" in intro name
  end.

Ltac equiv_simplify := repeat equiv_simplify_one.

Ltac equivify_tac :=
  match goal with
    | [ s : Equivalence ?A, H : ?R ?x ?y |- _ ] => change R with (@equiv A R s) in H
    | [ s : Equivalence ?A |- context C [ ?R ?x ?y ] ] => change (R x y) with (@equiv A R s x y)
  end.

Ltac equivify := repeat equivify_tac.

(** Every equivalence relation gives rise to a morphism, as it is transitive and symmetric. *)

Instance [ sa : ! Equivalence ] => equiv_morphism : Morphism (equiv ++> equiv ++> iff) equiv :=
  respect := respect.

(** The partial application too as it is reflexive. *)

Instance [ sa : ! Equivalence A ] (x : A) => 
  equiv_partial_app_morphism : Morphism (equiv ++> iff) (equiv x) :=
  respect := respect. 

Definition type_eq : relation Type :=
  fun x y => x = y.

Program Instance type_equivalence : Equivalence Type type_eq.

  Solve Obligations using constructor ; unfold type_eq ; program_simpl.

Ltac morphism_tac := try red ; unfold arrow ; intros ; program_simpl ; try tauto.

Ltac obligations_tactic ::= morphism_tac.

(** These are morphisms used to rewrite at the top level of a proof, 
   using [iff_impl_id_morphism] if the proof is in [Prop] and
   [eq_arrow_id_morphism] if it is in Type. *)

Program Instance iff_impl_id_morphism : 
  Morphism (iff ++> impl) id.

(* Program Instance eq_arrow_id_morphism : ? Morphism (eq +++> arrow) id. *)

(** Partial equivs don't require reflexivity so we can build a partial equiv on the function space. *)

Class PartialEquivalence (carrier : Type) (pequiv : relation carrier) :=
  pequiv_prf :> PER carrier pequiv.

(** Overloaded notation for partial equiv equivalence. *)

(* Infix "=~=" := pequiv (at level 70, no associativity) : type_scope. *)

(** Reset the default Program tactic. *)

Ltac obligations_tactic ::= program_simpl.

(** Default relation on a given support. *)

Class DefaultRelation A := default_relation : relation A.

(** Every [Equivalence] gives a default relation, if no other is given (lowest priority). *)

Instance [ ! Equivalence A R ] => 
  equivalence_default : DefaultRelation A | 4 := 
  default_relation := R.

