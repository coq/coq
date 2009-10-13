(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Finite sets library.
 * Authors: Pierre Letouzey and Jean-Christophe Filliâtre
 * Institution: LRI, CNRS UMR 8623 - Université Paris Sud
 *              91405 Orsay, France *)

(* $Id$ *)

Require Import OrderedType2 DecidableType2Ex.
Require Import ZArith NArith Ndec Compare_dec.

(** * Examples of Ordered Type structures. *)

(** First, a particular case of [OrderedType] where
    the equality is the usual one of Coq. *)

Module Type UsualOrderedType.
 Include Type UsualDecidableType.

 Parameter Inline lt : t -> t -> Prop.
 Instance lt_strorder : StrictOrder lt.
 (* The following is useless since eq is Leibniz, but should be there
    for subtyping... *)
 Instance lt_compat : Proper (eq==>eq==>iff) lt.

 Parameter compare : t -> t -> comparison.
 Axiom compare_spec : forall x y, Cmp eq lt (compare x y) x y.

End UsualOrderedType.

(** a [UsualOrderedType] is in particular an [OrderedType]. *)

Module UOT_to_OT (U:UsualOrderedType) <: OrderedType := U.

(** [nat] is an ordered type with respect to the usual order on natural numbers. *)

Module Nat_as_OT <: UsualOrderedType.

  Definition t := nat.
  Definition eq := @eq nat.
  Definition lt := lt.
  Definition compare := nat_compare.
  Definition eq_dec := eq_nat_dec.

  Program Instance eq_equiv : Equivalence eq.

  Instance lt_strorder : StrictOrder lt.
  Proof.
  constructor; [exact lt_irrefl|exact lt_trans].
  Qed.

  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
  unfold eq in *; repeat red; intros; subst; auto.
  Qed.

  Lemma compare_spec : forall x y, Cmp eq lt (compare x y) x y.
  Proof.
  intros.
  unfold Cmp, flip, lt, eq. destruct (compare x y) as [ ]_eqn:H.
  apply nat_compare_eq; auto.
  apply nat_compare_Lt_lt; auto.
  apply nat_compare_Gt_gt; auto.
  Qed.

End Nat_as_OT.


(** [Z] is an ordered type with respect to the usual order on integers. *)

Module Z_as_OT <: UsualOrderedType.

  Definition t := Z.
  Definition eq := @eq Z.
  Definition lt := Zlt.
  Definition compare := Zcompare.
  Definition eq_dec := Z_eq_dec.

  Program Instance eq_equiv : Equivalence eq.

  Instance lt_strorder : StrictOrder lt.
  Proof.
  constructor; [exact Zlt_irrefl | exact Zlt_trans].
  Qed.

  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
  unfold eq in *; repeat red; intros; subst; auto.
  Qed.

  Lemma compare_spec : forall x y, Cmp eq lt (compare x y) x y.
  Proof.
  intros.
  unfold Cmp, flip, lt, eq. destruct (compare x y) as [ ]_eqn:H.
  apply Zcompare_Eq_eq; auto.
  auto.
  apply Zgt_lt; auto.
  Qed.

End Z_as_OT.

(** [positive] is an ordered type with respect to the usual order
    on natural numbers. *)

Module Positive_as_OT <: UsualOrderedType.
  Definition t:=positive.
  Definition eq:=@eq positive.
  Definition lt:=Plt.
  Definition compare x y := Pcompare x y Eq.

  Program Instance eq_equiv : Equivalence eq.

  Instance lt_strorder : StrictOrder lt.
  Proof.
  constructor; [exact Plt_irrefl | exact Plt_trans].
  Qed.

  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
  unfold eq in *; repeat red; intros; subst; auto.
  Qed.

  Lemma compare_spec : forall x y, Cmp eq lt (compare x y) x y.
  Proof.
  intros.
  unfold Cmp, flip, lt, eq. destruct (compare x y) as [ ]_eqn:H.
  apply Pcompare_Eq_eq; auto.
  auto.
  apply ZC1; auto.
  Qed.

  Definition eq_dec : forall x y, { eq x y } + { ~ eq x y }.
  Proof.
   intros; unfold eq; decide equality.
  Defined.

End Positive_as_OT.


(** [N] is an ordered type with respect to the usual order
    on natural numbers. *)

Module N_as_OT <: UsualOrderedType.
  Definition t:=N.
  Definition eq:=@eq N.
  Definition lt:=Nlt.
  Definition compare:=Ncompare.

  Program Instance eq_equiv : Equivalence eq.

  Instance lt_strorder : StrictOrder lt.
  Proof.
  constructor; [exact Nlt_irrefl | exact Nlt_trans].
  Qed.

  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
  unfold eq in *; repeat red; intros; subst; auto.
  Qed.

  Lemma compare_spec : forall x y, Cmp eq lt (compare x y) x y.
  Proof.
  intros.
  unfold Cmp, flip, lt, eq. destruct (compare x y) as [ ]_eqn:H.
  apply Ncompare_Eq_eq; auto.
  auto.
  apply Ngt_Nlt; auto.
  Qed.

  Definition eq_dec : forall x y, { eq x y } + { ~ eq x y }.
  Proof.
   intros. unfold eq. decide equality. apply Positive_as_OT.eq_dec.
  Defined.

End N_as_OT.


(** An OrderedType can now directly be seen as a DecidableType *)

Module OT_as_DT (O:OrderedType) <: DecidableType := O.

(** (Usual) Decidable Type for [nat], [positive], [N], [Z] *)

Module Nat_as_DT <: UsualDecidableType := Nat_as_OT.
Module Positive_as_DT <: UsualDecidableType := Positive_as_OT.
Module N_as_DT <: UsualDecidableType := N_as_OT.
Module Z_as_DT <: UsualDecidableType := Z_as_OT.




(** From two ordered types, we can build a new OrderedType
   over their cartesian product, using the lexicographic order. *)

Module PairOrderedType(O1 O2:OrderedType) <: OrderedType.

 Definition t := prod O1.t O2.t.

 Definition eq := ProdRel O1.eq O2.eq.

 Definition lt x y :=
    O1.lt (fst x) (fst y) \/
    (O1.eq (fst x) (fst y) /\ O2.lt (snd x) (snd y)).

 Instance eq_equiv : Equivalence eq.

 Instance lt_strorder : StrictOrder lt.
 Proof.
 split.
 (* irreflexive *)
 intros (x1,x2); compute. destruct 1.
 apply (StrictOrder_Irreflexive x1); auto.
 apply (StrictOrder_Irreflexive x2); intuition.
 (* transitive *)
 intros (x1,x2) (y1,y2) (z1,z2); unfold eq, lt; simpl; intuition.
 left; etransitivity; eauto.
 left; rewrite <- H0; auto.
 left; rewrite H; auto.
 right; split; eauto. etransitivity; eauto.
 Qed.

 Instance lt_compat : Proper (eq==>eq==>iff) lt.
 Proof.
 intros (x1,x2) (x1',x2') (X1,X2) (y1,y2) (y1',y2') (Y1,Y2).
 unfold lt; simpl in *.
 rewrite X1,X2,Y1,Y2; intuition.
 Qed.

 Definition compare x y :=
  match O1.compare (fst x) (fst y) with
   | Eq => O2.compare (snd x) (snd y)
   | Lt => Lt
   | Gt => Gt
  end.

 Lemma compare_spec : forall x y, Cmp eq lt (compare x y) x y.
 Proof.
 intros (x1,x2) (y1,y2); unfold Cmp, flip, compare, eq, lt; simpl.
 generalize (O1.compare_spec x1 y1); destruct (O1.compare x1 y1); intros; auto.
 generalize (O2.compare_spec x2 y2); destruct (O2.compare x2 y2); intros; auto.
 Qed.

 Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
 Proof.
 intros; generalize (compare_spec x y); destruct (compare x y).
 left; auto.
 right. intros E; rewrite E in *.
  apply (StrictOrder_Irreflexive y); auto.
 right. intros E; rewrite E in *.
  apply (StrictOrder_Irreflexive y); auto.
 Defined.

End PairOrderedType.

