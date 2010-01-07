(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

Require Import Basics OrdersTac.
Require Export Orders.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Properties of [OrderedTypeFull] *)

Module OrderedTypeFullFacts (Import O:OrderedTypeFull').

 Module OrderTac := OTF_to_OrderTac O.
 Ltac order := OrderTac.order.
 Ltac iorder := intuition order.

 Instance le_compat : Proper (eq==>eq==>iff) le.
 Proof. repeat red; iorder. Qed.

 Instance le_preorder : PreOrder le.
 Proof. split; red; order. Qed.

 Instance le_order : PartialOrder eq le.
 Proof. compute; iorder. Qed.

 Instance le_antisym : Antisymmetric _ eq le.
 Proof. apply partial_order_antisym; auto with *. Qed.

 Lemma le_not_gt_iff : forall x y, x<=y <-> ~y<x.
 Proof. iorder. Qed.

 Lemma lt_not_ge_iff : forall x y, x<y <-> ~y<=x.
 Proof. iorder. Qed.

 Lemma le_or_gt : forall x y, x<=y \/ y<x.
 Proof. intros. rewrite le_lteq; destruct (O.compare_spec x y); auto. Qed.

 Lemma lt_or_ge : forall x y, x<y \/ y<=x.
 Proof. intros. rewrite le_lteq; destruct (O.compare_spec x y); iorder. Qed.

 Lemma eq_is_le_ge : forall x y, x==y <-> x<=y /\ y<=x.
 Proof. iorder. Qed.

End OrderedTypeFullFacts.


(** * Properties of [OrderedType] *)

Module OrderedTypeFacts (Import O: OrderedType').

  Module OrderTac := OT_to_OrderTac O.
  Ltac order := OrderTac.order.

  Notation "x <= y" := (~lt y x) : order.
  Infix "?=" := compare (at level 70, no associativity) : order.

  Local Open Scope order.

  Tactic Notation "elim_compare" constr(x) constr(y) :=
   destruct (compare_spec x y).

  Tactic Notation "elim_compare" constr(x) constr(y) "as" ident(h) :=
   destruct (compare_spec x y) as [h|h|h].

  (** The following lemmas are either re-phrasing of [eq_equiv] and
      [lt_strorder] or immediately provable by [order]. Interest:
      compatibility, test of order, etc *)

  Definition eq_refl (x:t) : x==x := Equivalence_Reflexive x.

  Definition eq_sym (x y:t) : x==y -> y==x := Equivalence_Symmetric x y.

  Definition eq_trans (x y z:t) : x==y -> y==z -> x==z :=
   Equivalence_Transitive x y z.

  Definition lt_trans (x y z:t) : x<y -> y<z -> x<z :=
   StrictOrder_Transitive x y z.

  Definition lt_irrefl (x:t) : ~x<x := StrictOrder_Irreflexive x.

  (** Some more about [compare] *)

  Lemma compare_eq_iff : forall x y, (x ?= y) = Eq <-> x==y.
  Proof.
   intros; elim_compare x y; intuition; try discriminate; order.
  Qed.

  Lemma compare_lt_iff : forall x y, (x ?= y) = Lt <-> x<y.
  Proof.
   intros; elim_compare x y; intuition; try discriminate; order.
  Qed.

  Lemma compare_gt_iff : forall x y, (x ?= y) = Gt <-> y<x.
  Proof.
   intros; elim_compare x y; intuition; try discriminate; order.
  Qed.

  Lemma compare_ge_iff : forall x y, (x ?= y) <> Lt <-> y<=x.
  Proof.
   intros; rewrite compare_lt_iff; intuition.
  Qed.

  Lemma compare_le_iff : forall x y, (x ?= y) <> Gt <-> x<=y.
  Proof.
   intros; rewrite compare_gt_iff; intuition.
  Qed.

  Hint Rewrite compare_eq_iff compare_lt_iff compare_gt_iff : order.

  Instance compare_compat : Proper (eq==>eq==>Logic.eq) compare.
  Proof.
  intros x x' Hxx' y y' Hyy'.
  elim_compare x' y'; autorewrite with order; order.
  Qed.

  Lemma compare_refl : forall x, (x ?= x) = Eq.
  Proof.
   intros; elim_compare x x; auto; order.
  Qed.

  Lemma compare_antisym : forall x y, (y ?= x) = CompOpp (x ?= y).
  Proof.
   intros; elim_compare x y; simpl; autorewrite with order; order.
  Qed.

  (** For compatibility reasons *)
  Definition eq_dec := eq_dec.

  Lemma lt_dec : forall x y : t, {lt x y} + {~ lt x y}.
  Proof.
   intros; assert (H:=compare_spec x y); destruct (compare x y);
    [ right | left | right ]; inversion_clear H; order.
  Defined.

  Definition eqb x y : bool := if eq_dec x y then true else false.

  Lemma if_eq_dec : forall x y (B:Type)(b b':B),
    (if eq_dec x y then b else b') =
    (match compare x y with Eq => b | _ => b' end).
  Proof.
  intros; destruct eq_dec; elim_compare x y; auto; order.
  Qed.

  Lemma eqb_alt :
    forall x y, eqb x y = match compare x y with Eq => true | _ => false end.
  Proof.
  unfold eqb; intros; apply if_eq_dec.
  Qed.

  Instance eqb_compat : Proper (eq==>eq==>Logic.eq) eqb.
  Proof.
  intros x x' Hxx' y y' Hyy'.
  rewrite 2 eqb_alt, Hxx', Hyy'; auto.
  Qed.

End OrderedTypeFacts.






(** * Tests of the order tactic

    Is it at least capable of proving some basic properties ? *)

Module OrderedTypeTest (Import O:OrderedType').
  Module Import MO := OrderedTypeFacts O.
  Local Open Scope order.
  Lemma lt_not_eq x y : x<y -> ~x==y.  Proof. order. Qed.
  Lemma lt_eq x y z : x<y -> y==z -> x<z. Proof. order. Qed.
  Lemma eq_lt x y z : x==y -> y<z -> x<z. Proof. order. Qed.
  Lemma le_eq x y z : x<=y -> y==z -> x<=z. Proof. order. Qed.
  Lemma eq_le x y z : x==y -> y<=z -> x<=z. Proof. order. Qed.
  Lemma neq_eq x y z : ~x==y -> y==z -> ~x==z. Proof. order. Qed.
  Lemma eq_neq x y z : x==y -> ~y==z -> ~x==z. Proof. order. Qed.
  Lemma le_lt_trans x y z : x<=y -> y<z -> x<z. Proof. order. Qed.
  Lemma lt_le_trans x y z : x<y -> y<=z -> x<z. Proof. order. Qed.
  Lemma le_trans x y z : x<=y -> y<=z -> x<=z. Proof. order. Qed.
  Lemma le_antisym x y : x<=y -> y<=x -> x==y. Proof. order. Qed.
  Lemma le_neq x y : x<=y -> ~x==y -> x<y. Proof. order. Qed.
  Lemma neq_sym x y : ~x==y -> ~y==x. Proof. order. Qed.
  Lemma lt_le x y : x<y -> x<=y. Proof. order. Qed.
  Lemma gt_not_eq x y : y<x -> ~x==y. Proof. order. Qed.
  Lemma eq_not_lt x y : x==y -> ~x<y. Proof. order. Qed.
  Lemma eq_not_gt x y : x==y -> ~ y<x. Proof. order. Qed.
  Lemma lt_not_gt x y : x<y -> ~ y<x. Proof. order. Qed.
  Lemma eq_is_nlt_ngt x y : x==y <-> ~x<y /\ ~y<x.
  Proof. intuition; order. Qed.
End OrderedTypeTest.



(** * Reversed OrderedTypeFull.

   we can switch the orientation of the order. This is used for
   example when deriving properties of [min] out of the ones of [max]
   (see [GenericMinMax]).
*)

Module OrderedTypeRev (O:OrderedTypeFull) <: OrderedTypeFull.

Definition t := O.t.
Definition eq := O.eq.
Instance eq_equiv : Equivalence eq.
Definition eq_dec := O.eq_dec.

Definition lt := flip O.lt.
Definition le := flip O.le.

Instance lt_strorder: StrictOrder lt.
Proof. unfold lt; auto with *. Qed.
Instance lt_compat : Proper (eq==>eq==>iff) lt.
Proof. unfold lt; auto with *. Qed.

Lemma le_lteq : forall x y, le x y <-> lt x y \/ eq x y.
Proof. intros; unfold le, lt, flip. rewrite O.le_lteq; intuition. Qed.

Definition compare := flip O.compare.

Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
Proof.
intros; unfold compare, eq, lt, flip.
destruct (O.compare_spec y x); auto with relations.
Qed.

End OrderedTypeRev.

