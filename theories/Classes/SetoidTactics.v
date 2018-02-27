(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Tactics for typeclass-based setoids.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

Require Coq.Classes.CRelationClasses Coq.Classes.CMorphisms.
Require Import Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Require Export Coq.Classes.RelationClasses Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.Equivalence Coq.Program.Basics.

Generalizable Variables A R.

Export ProperNotations.

Set Implicit Arguments.
Unset Strict Implicit.

(** Default relation on a given support. Can be used by tactics
   to find a sensible default relation on any carrier. Users can
   declare an [Instance def : DefaultRelation A RA] anywhere to
   declare default relations. *)

Class DefaultRelation A (R : relation A).

(** To search for the default relation, just call [default_relation]. *)

Definition default_relation `{DefaultRelation A R} := R.

(** Every [Equivalence] gives a default relation, if no other is given
  (lowest priority). *)

Instance equivalence_default `(Equivalence A R) : DefaultRelation R | 4.

(** The setoid_replace tactics in Ltac, defined in terms of default relations
  and the setoid_rewrite tactic. *)

Ltac setoidreplace H t :=
  let Heq := fresh "Heq" in
    cut(H) ; unfold default_relation ; [ intro Heq ; setoid_rewrite Heq ; clear Heq | t ].

Ltac setoidreplacein H H' t :=
  let Heq := fresh "Heq" in
    cut(H) ; unfold default_relation ; [ intro Heq ; setoid_rewrite Heq in H' ; clear Heq | t ].

Ltac setoidreplaceinat H H' t occs :=
  let Heq := fresh "Heq" in
    cut(H) ; unfold default_relation ; [ intro Heq ; setoid_rewrite Heq in H' at occs ; clear Heq | t ].

Ltac setoidreplaceat H t occs :=
  let Heq := fresh "Heq" in
    cut(H) ; unfold default_relation ; [ intro Heq ; setoid_rewrite Heq at occs ; clear Heq | t ].

Tactic Notation "setoid_replace" constr(x) "with" constr(y) :=
  setoidreplace (default_relation x y) idtac.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
  "at" int_or_var_list(o) :=
  setoidreplaceat (default_relation x y) idtac o.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
  "in" hyp(id) :=
  setoidreplacein (default_relation x y) id idtac.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
  "in" hyp(id)
  "at" int_or_var_list(o) :=
  setoidreplaceinat (default_relation x y) id idtac o.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
  "by" tactic3(t) :=
  setoidreplace (default_relation x y) ltac:(t).

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
  "at" int_or_var_list(o)
  "by" tactic3(t) :=
  setoidreplaceat (default_relation x y) ltac:(t) o.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
  "in" hyp(id)
  "by" tactic3(t) :=
  setoidreplacein (default_relation x y) id ltac:(t).

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
  "in" hyp(id)
  "at" int_or_var_list(o)
  "by" tactic3(t) :=
  setoidreplaceinat (default_relation x y) id ltac:(t) o.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
  "using" "relation" constr(rel) :=
  setoidreplace (rel x y) idtac.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
  "using" "relation" constr(rel)
  "at" int_or_var_list(o) :=
  setoidreplaceat (rel x y) idtac o.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
  "using" "relation" constr(rel)
  "by" tactic3(t) :=
  setoidreplace (rel x y) ltac:(t).

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
  "using" "relation" constr(rel)
  "at" int_or_var_list(o)
  "by" tactic3(t) :=
  setoidreplaceat (rel x y) ltac:(t) o.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
  "using" "relation" constr(rel)
  "in" hyp(id) :=
  setoidreplacein (rel x y) id idtac.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
  "using" "relation" constr(rel)
  "in" hyp(id)
  "at" int_or_var_list(o) :=
  setoidreplaceinat (rel x y) id idtac o.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
  "using" "relation" constr(rel)
  "in" hyp(id)
  "by" tactic3(t) :=
  setoidreplacein (rel x y) id ltac:(t).

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
  "using" "relation" constr(rel)
  "in" hyp(id)
  "at" int_or_var_list(o)
  "by" tactic3(t) :=
  setoidreplaceinat (rel x y) id ltac:(t) o.

(** The [add_morphism_tactic] tactic is run at each [Add Morphism]
   command before giving the hand back to the user to discharge the
   proof. It essentially amounts to unfold the right amount of
   [respectful] calls and substitute leibniz equalities. One can
   redefine it using [Ltac add_morphism_tactic ::= t]. *)

Require Import Coq.Program.Tactics.

Local Open Scope signature_scope.

Ltac red_subst_eq_morphism concl :=
  match concl with
    | @Logic.eq ?A ==> ?R' => red ; intros ; subst ; red_subst_eq_morphism R'
    | ?R ==> ?R' => red ; intros ; red_subst_eq_morphism R'
    | _ => idtac
  end.

Ltac destruct_proper :=
  match goal with
    | [ |- @Proper ?A ?R ?m ] => red
  end.

Ltac reverse_arrows x :=
  match x with
    | @Logic.eq ?A ==> ?R' => revert_last ; reverse_arrows R'
    | ?R ==> ?R' => do 3 revert_last ; reverse_arrows R'
    | _ => idtac
  end.

Ltac default_add_morphism_tactic :=
  unfold flip ; intros ;
  (try destruct_proper) ;
  match goal with
    | [ |- (?x ==> ?y) _ _ ] => red_subst_eq_morphism (x ==> y) ; reverse_arrows (x ==> y)
  end.

Ltac add_morphism_tactic := default_add_morphism_tactic.

Obligation Tactic := program_simpl.

(* Notation "'Morphism' s t " := (@Proper _ (s%signature) t) (at level 10, s at next level, t at next level). *)
