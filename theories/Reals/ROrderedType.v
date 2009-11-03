(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Rbase DecidableType2 OrderedType2 OrderedType2Facts.

Local Open Scope R_scope.

(** * DecidableType structure for real numbers *)

Lemma Req_dec : forall r1 r2:R, {r1 = r2} + {r1 <> r2}.
Proof.
  intros; generalize (total_order_T r1 r2) Rlt_dichotomy_converse;
    intuition eauto 3.
Qed.


Module R_as_MiniDT <: MiniDecidableType.
 Definition t := R.
 Definition eq_dec := Req_dec.
End R_as_MiniDT.

Module R_as_DT <: UsualDecidableType := Make_UDT R_as_MiniDT.

(** Note that [R_as_DT] can also be seen as a [DecidableType]
    and a [DecidableTypeOrig]. *)



(** * OrderedType structure for binary integers *)



Definition Rcompare x y :=
 match total_order_T x y with
  | inleft (left _) => Lt
  | inleft (right _) => Eq
  | inright _ => Gt
 end.

Lemma Rcompare_spec : forall x y, CompSpec eq Rlt x y (Rcompare x y).
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
Ltac r_order :=
 change (@eq R) with ROrder.OrderElts.eq in *;
 ROrder.order.

(** Note that [z_order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)

