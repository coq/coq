(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Bool Basics OrdersTac.
Require Export Orders.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Properties of [compare] *)

Module Type CompareFacts (Import O:DecStrOrder').

 Local Infix "?=" := compare (at level 70, no associativity).

 Lemma compare_eq_iff x y : (x ?= y) = Eq <-> x==y.
 Proof.
 case compare_spec; intro H; split; try easy; intro EQ;
  contradict H; rewrite EQ; apply irreflexivity.
 Qed.

 Lemma compare_eq x y : (x ?= y) = Eq -> x==y.
 Proof.
 apply compare_eq_iff.
 Qed.

 Lemma compare_lt_iff x y : (x ?= y) = Lt <-> x<y.
 Proof.
  case compare_spec; intro H; split; try easy; intro LT;
  contradict LT; rewrite H; apply irreflexivity.
 Qed.

 Lemma compare_gt_iff x y : (x ?= y) = Gt <-> y<x.
 Proof.
 case compare_spec; intro H; split; try easy; intro LT;
  contradict LT; rewrite H; apply irreflexivity.
 Qed.

 Lemma compare_nlt_iff x y : (x ?= y) <> Lt <-> ~(x<y).
 Proof.
 rewrite compare_lt_iff; intuition.
 Qed.

 Lemma compare_ngt_iff x y : (x ?= y) <> Gt <-> ~(y<x).
 Proof.
 rewrite compare_gt_iff; intuition.
 Qed.

 Hint Rewrite compare_eq_iff compare_lt_iff compare_gt_iff : order.

 Instance compare_compat : Proper (eq==>eq==>Logic.eq) compare.
 Proof.
 intros x x' Hxx' y y' Hyy'.
 case (compare_spec x' y'); autorewrite with order; now rewrite Hxx', Hyy'.
 Qed.

 Lemma compare_refl x : (x ?= x) = Eq.
 Proof.
 case compare_spec; intros; trivial; now elim irreflexivity with x.
 Qed.

 Lemma compare_antisym x y : (y ?= x) = CompOpp (x ?= y).
 Proof.
 case (compare_spec x y); simpl; autorewrite with order;
  trivial; now symmetry.
 Qed.

End CompareFacts.


 (** * Properties of [OrderedTypeFull] *)

Module Type OrderedTypeFullFacts (Import O:OrderedTypeFull').

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

 Include CompareFacts O.

 Lemma compare_le_iff x y : compare x y <> Gt <-> x<=y.
 Proof.
 rewrite le_not_gt_iff. apply compare_ngt_iff.
 Qed.

 Lemma compare_ge_iff x y : compare x y <> Lt <-> y<=x.
 Proof.
 rewrite le_not_gt_iff. apply compare_nlt_iff.
 Qed.

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

  Include CompareFacts O.
  Notation compare_le_iff := compare_ngt_iff (only parsing).
  Notation compare_ge_iff := compare_nlt_iff (only parsing).

  (** For compatibility reasons *)
  Definition eq_dec := eq_dec.

  Lemma lt_dec : forall x y : t, {lt x y} + {~ lt x y}.
  Proof.
   intros x y; destruct (CompSpec2Type (compare_spec x y));
    [ right | left | right ]; order.
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
Program Instance eq_equiv : Equivalence eq.
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

Unset Implicit Arguments.

(** * Order relations derived from a [compare] function.

  We factorize here some common properties for ZArith, NArith
  and co, where [lt] and [le] are defined in terms of [compare].
  Note that we do not require anything here concerning compatibility
  of [compare] w.r.t [eq], nor anything concerning transitivity.
*)

Module Type CompareBasedOrder (Import E:EqLtLe')(Import C:HasCmp E).
 Include CmpNotation E C.
 Include IsEq E.
 Axiom compare_eq_iff : forall x y, (x ?= y) = Eq <-> x == y.
 Axiom compare_lt_iff : forall x y, (x ?= y) = Lt <-> x < y.
 Axiom compare_le_iff : forall x y, (x ?= y) <> Gt <-> x <= y.
 Axiom compare_antisym : forall x y, (y ?= x) = CompOpp (x ?= y).
End CompareBasedOrder.

Module Type CompareBasedOrderFacts
 (Import E:EqLtLe')
 (Import C:HasCmp E)
 (Import O:CompareBasedOrder E C).

 Lemma compare_spec x y : CompareSpec (x==y) (x<y) (y<x) (x?=y).
 Proof.
  case_eq (compare x y); intros H; constructor.
  now apply compare_eq_iff.
  now apply compare_lt_iff.
  rewrite compare_antisym, CompOpp_iff in H. now apply compare_lt_iff.
 Qed.

 Lemma compare_eq x y : (x ?= y) = Eq -> x==y.
 Proof.
 apply compare_eq_iff.
 Qed.

 Lemma compare_refl x : (x ?= x) = Eq.
 Proof.
 now apply compare_eq_iff.
 Qed.

 Lemma compare_gt_iff x y : (x ?= y) = Gt <-> y<x.
 Proof.
 now rewrite <- compare_lt_iff, compare_antisym, CompOpp_iff.
 Qed.

 Lemma compare_ge_iff x y : (x ?= y) <> Lt <-> y<=x.
 Proof.
 now rewrite <- compare_le_iff, compare_antisym, CompOpp_iff.
 Qed.

 Lemma compare_ngt_iff x y : (x ?= y) <> Gt <-> ~(y<x).
 Proof.
 rewrite compare_gt_iff; intuition.
 Qed.

 Lemma compare_nlt_iff x y : (x ?= y) <> Lt <-> ~(x<y).
 Proof.
 rewrite compare_lt_iff; intuition.
 Qed.

 Lemma compare_nle_iff x y : (x ?= y) = Gt <-> ~(x<=y).
 Proof.
 rewrite <- compare_le_iff.
 destruct compare; split; easy || now destruct 1.
 Qed.

 Lemma compare_nge_iff x y : (x ?= y) = Lt <-> ~(y<=x).
 Proof.
 now rewrite <- compare_nle_iff, compare_antisym, CompOpp_iff.
 Qed.

 Lemma lt_irrefl x : ~ (x<x).
 Proof.
 now rewrite <- compare_lt_iff, compare_refl.
 Qed.

 Lemma lt_eq_cases n m : n <= m <-> n < m \/ n==m.
 Proof.
 rewrite <- compare_lt_iff, <- compare_le_iff, <- compare_eq_iff.
 destruct (n ?= m); now intuition.
 Qed.

End CompareBasedOrderFacts.

(** Basic facts about boolean comparisons *)

Module Type BoolOrderFacts
 (Import E:EqLtLe')
 (Import C:HasCmp E)
 (Import F:HasBoolOrdFuns' E)
 (Import O:CompareBasedOrder E C)
 (Import S:BoolOrdSpecs E F).

Include CompareBasedOrderFacts E C O.

(** Nota : apart from [eqb_compare] below, facts about [eqb]
  are in BoolEqualityFacts *)

(** Alternate specifications based on [BoolSpec] and [reflect] *)

Lemma leb_spec0 x y : reflect (x<=y) (x<=?y).
Proof.
 apply iff_reflect. symmetry. apply leb_le.
Defined.

Lemma leb_spec x y : BoolSpec (x<=y) (y<x) (x<=?y).
Proof.
 case leb_spec0; constructor; trivial.
 now rewrite <- compare_lt_iff, compare_nge_iff.
Qed.

Lemma ltb_spec0 x y : reflect (x<y) (x<?y).
Proof.
 apply iff_reflect. symmetry. apply ltb_lt.
Defined.

Lemma ltb_spec x y : BoolSpec (x<y) (y<=x) (x<?y).
Proof.
 case ltb_spec0; constructor; trivial.
 now rewrite <- compare_le_iff, compare_ngt_iff.
Qed.

(** Negated variants of the specifications *)

Lemma leb_nle x y : x <=? y = false <-> ~ (x <= y).
Proof.
now rewrite <- not_true_iff_false, leb_le.
Qed.

Lemma leb_gt x y : x <=? y = false <-> y < x.
Proof.
now rewrite leb_nle, <- compare_lt_iff, compare_nge_iff.
Qed.

Lemma ltb_nlt x y : x <? y = false <-> ~ (x < y).
Proof.
now rewrite <- not_true_iff_false, ltb_lt.
Qed.

Lemma ltb_ge x y : x <? y = false <-> y <= x.
Proof.
now rewrite ltb_nlt, <- compare_le_iff, compare_ngt_iff.
Qed.

(** Basic equality laws for boolean tests *)

Lemma leb_refl x : x <=? x = true.
Proof.
apply leb_le. apply lt_eq_cases. now right.
Qed.

Lemma leb_antisym x y : y <=? x = negb (x <? y).
Proof.
apply eq_true_iff_eq. now rewrite negb_true_iff, leb_le, ltb_ge.
Qed.

Lemma ltb_irrefl x : x <? x = false.
Proof.
apply ltb_ge. apply lt_eq_cases. now right.
Qed.

Lemma ltb_antisym x y : y <? x = negb (x <=? y).
Proof.
apply eq_true_iff_eq. now rewrite negb_true_iff, ltb_lt, leb_gt.
Qed.

(** Relation bewteen [compare] and the boolean comparisons *)

Lemma eqb_compare x y :
 (x =? y) = match compare x y with Eq => true | _ => false end.
Proof.
apply eq_true_iff_eq. rewrite eqb_eq, <- compare_eq_iff.
now destruct compare.
Qed.

Lemma ltb_compare x y :
 (x <? y) = match compare x y with Lt => true | _ => false end.
Proof.
apply eq_true_iff_eq. rewrite ltb_lt, <- compare_lt_iff.
now destruct compare.
Qed.

Lemma leb_compare x y :
 (x <=? y) = match compare x y with Gt => false | _ => true end.
Proof.
apply eq_true_iff_eq. rewrite leb_le, <- compare_le_iff.
now destruct compare.
Qed.

End BoolOrderFacts.
