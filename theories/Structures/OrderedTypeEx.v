(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import OrderedType.
Require Import ZArith.
Require Import Omega.
Require Import NArith Ndec.
Require Import Compare_dec.

(** * Examples of Ordered Type structures. *)

(** First, a particular case of [OrderedType] where
    the equality is the usual one of Coq. *)

Module Type UsualOrderedType.
 Parameter Inline t : Type.
 Definition eq := @eq t.
 Parameter Inline lt : t -> t -> Prop.
 Definition eq_refl := @eq_refl t.
 Definition eq_sym := @eq_sym t.
 Definition eq_trans := @eq_trans t.
 Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
 Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
 Parameter compare : forall x y : t, Compare lt eq x y.
 Parameter eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
End UsualOrderedType.

(** a [UsualOrderedType] is in particular an [OrderedType]. *)

Module UOT_to_OT (U:UsualOrderedType) <: OrderedType := U.

(** [nat] is an ordered type with respect to the usual order on natural numbers. *)

Module Nat_as_OT <: UsualOrderedType.

  Definition t := nat.

  Definition eq := @eq nat.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt := lt.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. unfold lt; intros; apply lt_trans with y; auto. Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. unfold lt, eq; intros; omega. Qed.

  Definition compare x y : Compare lt eq x y.
  Proof.
    case_eq (Nat.compare x y); intro.
    - apply EQ. now apply nat_compare_eq.
    - apply LT. now apply nat_compare_Lt_lt.
    - apply GT. now apply nat_compare_Gt_gt.
  Defined.

  Definition eq_dec := eq_nat_dec.

End Nat_as_OT.


(** [Z] is an ordered type with respect to the usual order on integers. *)

Local Open Scope Z_scope.

Module Z_as_OT <: UsualOrderedType.

  Definition t := Z.
  Definition eq := @eq Z.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt (x y:Z) := (x<y).

  Lemma lt_trans : forall x y z, x<y -> y<z -> x<z.
  Proof. intros; omega. Qed.

  Lemma lt_not_eq : forall x y, x<y -> ~ x=y.
  Proof. intros; omega. Qed.

  Definition compare x y : Compare lt eq x y.
  Proof.
    case_eq (x ?= y); intro.
    - apply EQ. now apply Z.compare_eq.
    - apply LT. assumption.
    - apply GT. now apply Z.gt_lt.
  Defined.

  Definition eq_dec := Z.eq_dec.

End Z_as_OT.

(** [positive] is an ordered type with respect to the usual order on natural numbers. *)

Local Open Scope positive_scope.

Module Positive_as_OT <: UsualOrderedType.
  Definition t:=positive.
  Definition eq:=@eq positive.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt := Pos.lt.

  Definition lt_trans := Pos.lt_trans.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
  intros x y H. contradict H. rewrite H. apply Pos.lt_irrefl.
  Qed.

  Definition compare x y : Compare lt eq x y.
  Proof.
  case_eq (x ?= y); intros H.
  - apply EQ. now apply Pos.compare_eq.
  - apply LT; assumption.
  - apply GT. now apply Pos.gt_lt.
  Defined.

  Definition eq_dec := Pos.eq_dec.

End Positive_as_OT.


(** [N] is an ordered type with respect to the usual order on natural numbers. *)

Module N_as_OT <: UsualOrderedType.
  Definition t:=N.
  Definition eq:=@eq N.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt := N.lt.
  Definition lt_trans := N.lt_trans.
  Definition lt_not_eq := N.lt_neq.

  Definition compare x y : Compare lt eq x y.
  Proof.
  case_eq (x ?= y)%N; intro.
  - apply EQ. now apply N.compare_eq.
  - apply LT. assumption.
  - apply GT. now apply N.gt_lt.
  Defined.

  Definition eq_dec := N.eq_dec.

End N_as_OT.


(** From two ordered types, we can build a new OrderedType
   over their cartesian product, using the lexicographic order. *)

Module PairOrderedType(O1 O2:OrderedType) <: OrderedType.
 Module MO1:=OrderedTypeFacts(O1).
 Module MO2:=OrderedTypeFacts(O2).

 Definition t := prod O1.t O2.t.

 Definition eq x y := O1.eq (fst x) (fst y) /\ O2.eq (snd x) (snd y).

 Definition lt x y :=
    O1.lt (fst x) (fst y) \/
    (O1.eq (fst x) (fst y) /\ O2.lt (snd x) (snd y)).

 Lemma eq_refl : forall x : t, eq x x.
 Proof.
 intros (x1,x2); red; simpl; auto.
 Qed.

 Lemma eq_sym : forall x y : t, eq x y -> eq y x.
 Proof.
 intros (x1,x2) (y1,y2); unfold eq; simpl; intuition.
 Qed.

 Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
 Proof.
 intros (x1,x2) (y1,y2) (z1,z2); unfold eq; simpl; intuition eauto.
 Qed.

 Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
 Proof.
 intros (x1,x2) (y1,y2) (z1,z2); unfold eq, lt; simpl; intuition.
 left; eauto.
 left; eapply MO1.lt_eq; eauto.
 left; eapply MO1.eq_lt; eauto.
 right; split; eauto.
 Qed.

 Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
 Proof.
 intros (x1,x2) (y1,y2); unfold eq, lt; simpl; intuition.
 apply (O1.lt_not_eq H0 H1).
 apply (O2.lt_not_eq H3 H2).
 Qed.

 Definition compare : forall x y : t, Compare lt eq x y.
 intros (x1,x2) (y1,y2).
 destruct (O1.compare x1 y1).
 apply LT; unfold lt; auto.
 destruct (O2.compare x2 y2).
 apply LT; unfold lt; auto.
 apply EQ; unfold eq; auto.
 apply GT; unfold lt; auto.
 apply GT; unfold lt; auto.
 Defined.

 Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
 Proof.
 intros; elim (compare x y); intro H; [ right | left | right ]; auto.
 auto using lt_not_eq.
 assert (~ eq y x); auto using lt_not_eq, eq_sym.
 Defined.

End PairOrderedType.


(** Even if [positive] can be seen as an ordered type with respect to the
  usual order (see above), we can also use a lexicographic order over bits
  (lower bits are considered first). This is more natural when using
  [positive] as indexes for sets or maps (see FSetPositive and FMapPositive. *)

Module PositiveOrderedTypeBits <: UsualOrderedType.
  Definition t:=positive.
  Definition eq:=@eq positive.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Fixpoint bits_lt (p q:positive) : Prop :=
   match p, q with
   | xH, xI _ => True
   | xH, _ => False
   | xO p, xO q => bits_lt p q
   | xO _, _ => True
   | xI p, xI q => bits_lt p q
   | xI _, _ => False
   end.

  Definition lt:=bits_lt.

  Lemma bits_lt_trans :
    forall x y z : positive, bits_lt x y -> bits_lt y z -> bits_lt x z.
  Proof.
  induction x.
  induction y; destruct z; simpl; eauto; intuition.
  induction y; destruct z; simpl; eauto; intuition.
  induction y; destruct z; simpl; eauto; intuition.
  Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
  exact bits_lt_trans.
  Qed.

  Lemma bits_lt_antirefl : forall x : positive, ~ bits_lt x x.
  Proof.
  induction x; simpl; auto.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
  intros; intro.
  rewrite <- H0 in H; clear H0 y.
  unfold lt in H.
  exact (bits_lt_antirefl x H).
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
  induction x; destruct y.
  - (* I I *)
    destruct (IHx y) as [l|e|g].
    apply LT; auto.
    apply EQ; rewrite e; red; auto.
    apply GT; auto.
  - (* I O *)
    apply GT; simpl; auto.
  - (* I H *)
    apply GT; simpl; auto.
  - (* O I *)
    apply LT; simpl; auto.
  - (* O O *)
    destruct (IHx y) as [l|e|g].
    apply LT; auto.
    apply EQ; rewrite e; red; auto.
    apply GT; auto.
  - (* O H *)
    apply LT; simpl; auto.
  - (* H I *)
    apply LT; simpl; auto.
  - (* H O *)
    apply GT; simpl; auto.
  - (* H H *)
    apply EQ; red; auto.
  Qed.

  Lemma eq_dec (x y: positive): {x = y} + {x <> y}.
  Proof.
  intros. case_eq (x ?= y); intros.
  - left. now apply Pos.compare_eq.
  - right. intro. subst y. now rewrite (Pos.compare_refl x) in *.
  - right. intro. subst y. now rewrite (Pos.compare_refl x) in *.
  Qed.

End PositiveOrderedTypeBits.
