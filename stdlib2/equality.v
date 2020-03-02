(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import prelude ssreflect prop.

(** [eq x y], or simply [x=y] expresses the equality of [x] and
    [y]. Both [x] and [y] must belong to the same type [A].
    The definition is inductive and states the reflexivity of the equality.
    The others properties (symmetry, transitivity, replacement of
    equals by equals) are proved below. The type of [x] and [y] can be
    made explicit using the notation [x = y :> A]. This is Leibniz equality
    as it expresses that [x] and [y] are equal iff every property on
    [A] which is true of [x] is also true of [y] *)

Reserved Notation "x = y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x = y" (at level 70, no associativity).
Reserved Notation "x = y = z"
(at level 70, no associativity, y at next level).

Inductive eq (A : Type) (x : A) : A -> Prop :=
  eq_refl : x = x :> A

where "x = y :> A" := (@eq A x y) : type_scope.

Hint Resolve eq_refl : core.

Register eq as core.eq.type.
Register eq_refl as core.eq.refl.
Register eq_ind as core.eq.ind.
Register eq_rect as core.eq.rect.

Reserved Notation "x <> y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x <> y" (at level 70, no associativity).

Notation "x = y" := (eq x y) : type_scope.
Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
Notation "x <> y" := (~ (x = y)) : type_scope.

Arguments eq {A} x _.
Prenex Implicits eq_refl.
Arguments eq_refl {A x}, {A} x.

Arguments eq_ind [A] x P _ y _.
Arguments eq_rec [A] x P _ y _.
Arguments eq_rect [A] x P _ y _.

Register eq as core.eq.type.
Register eq_refl as core.eq.refl.
Register eq_ind as core.eq.ind.
Register eq_rect as core.eq.rect.

Definition eq_rect_dep A (x: A) (P: forall y, x = y -> Type) (ih: P x (eq_refl x)) y (e: x = y) : P y e :=
  let: eq_refl := e in ih.

Section equality.

Context {A B : Type} (f : A -> B) {x y z : A}.

Definition eq_sym : x = y -> y = x :=
  fun e => let: eq_refl := e in eq_refl.

Definition eq_trans : x = y -> y = z -> x = z :=
  fun e => let: eq_refl := e in fun f => f.

Definition eq_congr1 : x = y -> f x = f y :=
  fun e => let: eq_refl := e in eq_refl.

End equality.

Register eq_sym as core.eq.sym.
Register eq_trans as core.eq.trans.
Register eq_congr1 as core.eq.congr.

Definition eq_rect_r A (x: A) (P: A -> Type) (ih: P x) y (e: y = x) : P y :=
  eq_rect x P ih y (eq_sym e).

Definition eq_rec_r := eq_rect_r.
Definition eq_ind_r := eq_rect_r.

Arguments eq_rect_r {A x} P _ {y} _.
Arguments eq_rec_r {A x} P _ {y} _.
Arguments eq_ind_r {A x} P _ {y} _.

Lemma neq_sym A (x y : A) : x <> y -> y <> x.
Proof. by move=> neq_xy /eq_sym. Qed.

(* A predicate for singleton types.                                           *)
Definition all_equal_to T (x0 : T) := forall x, unkeyed x = x0.

Ltac done :=
  trivial; hnf; intros; solve
   [ do ![solve [trivial | apply: equality.eq_sym; trivial]
         | discriminate | contradiction | split]
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].
