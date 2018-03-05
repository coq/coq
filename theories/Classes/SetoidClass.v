(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Typeclass-based setoids, tactics and standard instances.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

Set Implicit Arguments.
Unset Strict Implicit.

Generalizable Variables A.

Require Import Coq.Program.Program.

Require Import Relation_Definitions.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.

(** A setoid wraps an equivalence. *)

Class Setoid A := {
  equiv : relation A ;
  setoid_equiv :> Equivalence equiv }.

(* Too dangerous instance *)
(* Program Instance [ eqa : Equivalence A eqA ] =>  *)
(*   equivalence_setoid : Setoid A := *)
(*   equiv := eqA ; setoid_equiv := eqa. *)

(** Shortcuts to make proof search easier. *)

Definition setoid_refl `(sa : Setoid A) : Reflexive equiv.
Proof. typeclasses eauto. Qed.

Definition setoid_sym `(sa : Setoid A) : Symmetric equiv.
Proof. typeclasses eauto. Qed.

Definition setoid_trans `(sa : Setoid A) : Transitive equiv.
Proof. typeclasses eauto. Qed.

Existing Instance setoid_refl.
Existing Instance setoid_sym.
Existing Instance setoid_trans.

(** Standard setoids. *)

(* Program Instance eq_setoid : Setoid A := *)
(*   equiv := eq ; setoid_equiv := eq_equivalence. *)

Program Instance iff_setoid : Setoid Prop :=
  { equiv := iff ; setoid_equiv := iff_equivalence }.

(** Overloaded notations for setoid equivalence and inequivalence. Not to be confused with [eq] and [=]. *)

(** Subset objects should be first coerced to their underlying type, but that notation doesn't work in the standard case then. *)
(* Notation " x == y " := (equiv (x :>) (y :>)) (at level 70, no associativity) : type_scope. *)

Notation " x == y " := (equiv x y) (at level 70, no associativity) : type_scope.

Notation " x =/= y " := (complement equiv x y) (at level 70, no associativity) : type_scope.

(** Use the [clsubstitute] command which substitutes an equality in every hypothesis. *)

Ltac clsubst H :=
  lazymatch type of H with
    ?x == ?y => substitute H ; clear H x
  end.

Ltac clsubst_nofail :=
  match goal with
    | [ H : ?x == ?y |- _ ] => clsubst H ; clsubst_nofail
    | _ => idtac
  end.

(** [subst*] will try its best at substituting every equality in the goal. *)

Tactic Notation "clsubst" "*" := clsubst_nofail.

Lemma nequiv_equiv_trans : forall `{Setoid A} (x y z : A), x =/= y -> y == z -> x =/= z.
Proof with auto.
  intros; intro.
  assert(z == y) by (symmetry ; auto).
  assert(x == y) by (transitivity z ; eauto).
  contradiction.
Qed.

Lemma equiv_nequiv_trans : forall `{Setoid A} (x y z : A), x == y -> y =/= z -> x =/= z.
Proof.
  intros; intro.
  assert(y == x) by (symmetry ; auto).
  assert(y == z) by (transitivity x ; eauto).
  contradiction.
Qed.

Ltac setoid_simplify_one :=
  match goal with
    | [ H : (?x == ?x)%type |- _ ] => clear H
    | [ H : (?x == ?y)%type |- _ ] => clsubst H
    | [ |- (?x =/= ?y)%type ] => let name:=fresh "Hneq" in intro name
  end.

Ltac setoid_simplify := repeat setoid_simplify_one.

Ltac setoidify_tac :=
  match goal with
    | [ s : Setoid ?A, H : ?R ?x ?y |- _ ] => change R with (@equiv A R s) in H
    | [ s : Setoid ?A |- context C [ ?R ?x ?y ] ] => change (R x y) with (@equiv A R s x y)
  end.

Ltac setoidify := repeat setoidify_tac.

(** Every setoid relation gives rise to a morphism, in fact every partial setoid does. *)

Program Instance setoid_morphism `(sa : Setoid A) : Proper (equiv ++> equiv ++> iff) equiv :=
  proper_prf.

Program Instance setoid_partial_app_morphism `(sa : Setoid A) (x : A) : Proper (equiv ++> iff) (equiv x) :=
  proper_prf.

(** Partial setoids don't require reflexivity so we can build a partial setoid on the function space. *)

Class PartialSetoid (A : Type) :=
  { pequiv : relation A ; pequiv_prf :> PER pequiv }.

(** Overloaded notation for partial setoid equivalence. *)

Infix "=~=" := pequiv (at level 70, no associativity) : type_scope.

(** Reset the default Program tactic. *)

Obligation Tactic := program_simpl.
