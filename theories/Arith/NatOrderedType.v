(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Peano_dec Compare_dec
 DecidableType2 OrderedType2 OrderedType2Facts.


(** * DecidableType structure for Peano numbers *)

Module Nat_as_MiniDT <: MiniDecidableType.
 Definition t := nat.
 Definition eq_dec := eq_nat_dec.
End Nat_as_MiniDT.

Module Nat_as_DT <: UsualDecidableType := Make_UDT Nat_as_MiniDT.

(** Note that [Nat_as_DT] can also be seen as a [DecidableType]
    and a [DecidableTypeOrig]. *)



(** * OrderedType structure for Peano numbers *)

Module Nat_as_OT <: OrderedTypeFull.
 Include Nat_as_DT.
 Definition lt := lt.
 Definition le := le.
 Definition compare := nat_compare.

 Instance lt_strorder : StrictOrder lt.
 Proof. split; [ exact Lt.lt_irrefl | exact Lt.lt_trans ]. Qed.

 Instance lt_compat : Proper (Logic.eq==>Logic.eq==>iff) lt.
 Proof. repeat red; intros; subst; auto. Qed.

 Lemma le_lteq : forall x y, x <= y <-> x < y \/ x=y.
 Proof. intuition; subst; auto using Lt.le_lt_or_eq. Qed.

 Lemma compare_spec : forall x y, Cmp eq lt x y (compare x y).
 Proof.
 intros; unfold compare.
 destruct (nat_compare x y) as [ ]_eqn; constructor.
 apply nat_compare_eq; auto.
 apply nat_compare_Lt_lt; auto.
 apply nat_compare_Gt_gt; auto.
 Qed.

End Nat_as_OT.

(* Note that [Nat_as_OT] can also be seen as a [UsualOrderedType]
   and a [OrderedType] (and also as a [DecidableType]). *)



(** * An [order] tactic for Peano numbers *)

Module NatOrder := OTF_to_OrderTac Nat_as_OT.
Ltac nat_order :=
 change (@eq nat) with NatOrder.OrderElts.eq in *;
 NatOrder.order.

(** Note that [nat_order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)

