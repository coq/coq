(* -*- coq-prog-args: ("-emacs-U" "-nois") -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Tactics for typeclass-based setoids.
 *
 * Author: Matthieu Sozeau
 * Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
 *              91405 Orsay, France *)

(* $Id$ *)

Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Classes.Equivalence.
Require Export Coq.Relations.Relation_Definitions.

Set Implicit Arguments.
Unset Strict Implicit.

(** The setoid_replace tactics in Ltac, defined in terms of default relations [===def] and
   the setoid_rewrite tactic. *)

Ltac setoidreplace H t :=
  let Heq := fresh "Heq" in
    cut(H) ; unfold default_relation ; [ intro Heq ; setoid_rewrite Heq ; clear Heq | t ].

Ltac setoidreplacein H H' t :=
  let Heq := fresh "Heq" in
    cut(H) ; unfold default_relation ; [ intro Heq ; setoid_rewrite Heq in H' ; clear Heq | t ].

Tactic Notation "setoid_replace" constr(x) "with" constr(y) :=
  setoidreplace (x ===def y) idtac.

Tactic Notation "setoid_replace" constr(x) "with" constr(y) "in" hyp(id) :=
  setoidreplacein (x ===def y) id idtac.

Tactic Notation "setoid_replace" constr(x) "with" constr(y) "by" tactic(t) :=
  setoidreplace (x ===def y) ltac:t.

Tactic Notation "setoid_replace" constr(x) "with" constr(y) "in" hyp(id) "by" tactic(t) :=
  setoidreplacein (x ===def y) id ltac:t.

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

(** The [add_morphism_tactic] tactic is run at each [Add Morphism] command before giving the hand back
   to the user to discharge the proof. It essentially amounts to unfold the right amount of [respectful] calls
   and substitute leibniz equalities. One can redefine it using [Ltac add_morphism_tactic ::= t]. *)

Require Import Coq.Program.Tactics.

Open Local Scope signature_scope.

Ltac red_subst_eq_morphism concl :=
  match concl with
    | @Logic.eq ?A ==> ?R' => red ; intros ; subst ; red_subst_eq_morphism R'
    | ?R ==> ?R' => red ; intros ; red_subst_eq_morphism R'
    | _ => idtac
  end.

Ltac destruct_morphism :=
  match goal with
    | [ |- @Morphism ?A ?R ?m ] => red
  end.

Ltac reverse_arrows x :=
  match x with
    | @Logic.eq ?A ==> ?R' => revert_last ; reverse_arrows R'
    | ?R ==> ?R' => do 3 revert_last ; reverse_arrows R'
    | _ => idtac
  end.

Ltac default_add_morphism_tactic :=
  (try destruct_morphism) ;
  match goal with
    | [ |- (?x ==> ?y) _ _ ] => red_subst_eq_morphism (x ==> y) ; reverse_arrows (x ==> y)
  end.

Ltac add_morphism_tactic := default_add_morphism_tactic.
