(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file contains basic propositional connectives *)

Require Import prelude ssreflect.

(** Notations for propositional connectives *)

Reserved Notation "x <-> y" (at level 95, no associativity).
Reserved Notation "x \/ y" (at level 85, right associativity).
Reserved Notation "x ∨ y" (at level 85, right associativity).
Reserved Notation "x /\ y" (at level 80, right associativity).
Reserved Notation "x ∧ y" (at level 80, right associativity).
Reserved Notation "~ x" (at level 75, right associativity).
Reserved Notation "¬ x" (at level 75, right associativity).

(** [True] is the always true proposition *)

Variant True : Prop :=
  True_intro : True.

Register True as core.True.type.
Register True_intro as core.True.True_intro.
Register True_intro as core.True.I.

(** [False] is the always false proposition *)

Inductive False : Prop :=.

Register False as core.False.type.

(** [not A], written [~A], is the negation of [A] *)
Definition not (A : Prop) := A -> False.

Notation "~ x" := (not x) : type_scope.
Notation "¬ x" := (not x) : type_scope.

Register not as core.not.type.

(** Create the “core” hint database, and set its transparent state for
  variables and constants explicitely. *)
Create HintDb core.
Hint Variables Opaque : core.
Hint Constants Opaque : core.

Hint Unfold not: core.

(** [and A B], written [A /\ B], is the conjunction of [A] and [B]

    [and_intro p q] is a proof of [A /\ B] as soon as
    [p] is a proof of [A] and [q] a proof of [B]

    [and_proj1] and [and_proj2] are first and second projections of a conjunction *)

Record and (A B : Prop) : Prop :=
  and_intro { and_proj1 : A; and_proj2 : B }.

Notation "A /\ B" := (and A B) : type_scope.
Infix "∧" := and : type_scope.

Inductive or (A B: Prop) : Prop :=
| OrL of A
| OrR of B.

Infix "\/" := or : type_scope.
Infix "∨" := or : type_scope.

Register or as core.or.type.

Record iff (A B : Prop) : Prop :=
  iff_intro { iff_proj1 : A -> B; iff_proj2 : B -> A }.
Notation "A <-> B" := (iff A B) : type_scope.

(* View lemmas that don't use reflection.                                     *)

Section ApplyIff.

Variables P Q : Prop.
Hypothesis eqPQ : P <-> Q.

Lemma iffLR : P -> Q. Proof. by case: eqPQ. Qed.
Lemma iffRL : Q -> P. Proof. by case: eqPQ. Qed.

Lemma iffLRn : ~P -> ~Q. Proof. by move=> nP tQ; case: nP; case: eqPQ tQ. Qed.
Lemma iffRLn : ~Q -> ~P. Proof. by move=> nQ tP; case: nQ; case: eqPQ tP. Qed.

End ApplyIff.

Hint View for move/ iffLRn|2 iffRLn|2 iffLR|2 iffRL|2.
Hint View for apply/ iffRLn|2 iffLRn|2 iffRL|2 iffLR|2.

(** Existential quantification *)
Variant ex A (P: A -> Type) : Prop :=
| Ex a of P a.

Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists' '/ ' x .. y , '/ ' p ']'")
: type_scope.

Register ex as core.ex.type.

Variant ex2 A (P Q: A -> Type) : Prop :=
| Ex2 a of P a & Q a.

Notation "'exists2' x , p & q" := (ex2 (fun x => p) (fun x => q))
  (at level 200, x ident, p at level 200, right associativity) : type_scope.
Notation "'exists2' x : A , p & q" := (ex2 (A:=A) (fun x => p) (fun x => q))
  (at level 200, x ident, A at level 200, p at level 200, right associativity,
    format "'[' 'exists2'  '/  ' x  :  A ,  '/  ' '[' p  &  '/' q ']' ']'")
  : type_scope.
