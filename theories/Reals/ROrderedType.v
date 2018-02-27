(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Rbase Equalities Orders OrdersTac.

Local Open Scope R_scope.

(** * DecidableType structure for real numbers *)

Lemma Req_dec : forall r1 r2:R, {r1 = r2} + {r1 <> r2}.
Proof.
  intros; generalize (total_order_T r1 r2) Rlt_dichotomy_converse;
    intuition eauto.
Qed.

Definition Reqb r1 r2 := if Req_dec r1 r2 then true else false.
Lemma Reqb_eq : forall r1 r2, Reqb r1 r2 = true <-> r1=r2.
Proof.
 intros; unfold Reqb; destruct Req_dec as [EQ|NEQ]; auto with *.
 split; try discriminate. intro EQ; elim NEQ; auto.
Qed.

Module R_as_UBE <: UsualBoolEq.
 Definition t := R.
 Definition eq := @eq R.
 Definition eqb := Reqb.
 Definition eqb_eq := Reqb_eq.
End R_as_UBE.

Module R_as_DT <: UsualDecidableTypeFull := Make_UDTF R_as_UBE.

(** Note that the last module fulfills by subtyping many other
    interfaces, such as [DecidableType] or [EqualityType]. *)



(** Note that [R_as_DT] can also be seen as a [DecidableType]
    and a [DecidableTypeOrig]. *)



(** * OrderedType structure for binary integers *)



Definition Rcompare x y :=
 match total_order_T x y with
  | inleft (left _) => Lt
  | inleft (right _) => Eq
  | inright _ => Gt
 end.

Lemma Rcompare_spec : forall x y, CompareSpec (x=y) (x<y) (y<x) (Rcompare x y).
Proof.
 intros. unfold Rcompare.
 destruct total_order_T as [[H|H]|H]; auto.
Qed.

Module R_as_OT <: OrderedTypeFull.
 Include R_as_DT.
 Definition lt := Rlt.
 Definition le := Rle.
 Definition compare := Rcompare.

 Instance lt_strorder : StrictOrder Rlt.
 Proof. split; [ exact Rlt_irrefl | exact Rlt_trans ]. Qed.

 Instance lt_compat : Proper (Logic.eq==>Logic.eq==>iff) Rlt.
 Proof. repeat red; intros; subst; auto. Qed.

 Lemma le_lteq : forall x y, x <= y <-> x < y \/ x = y.
 Proof. unfold Rle; auto with *. Qed.

 Definition compare_spec := Rcompare_spec.

End R_as_OT.

(** Note that [R_as_OT] can also be seen as a [UsualOrderedType]
   and a [OrderedType] (and also as a [DecidableType]). *)



(** * An [order] tactic for real numbers *)

Module ROrder := OTF_to_OrderTac R_as_OT.
Ltac r_order := ROrder.order.

(** Note that [r_order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)

