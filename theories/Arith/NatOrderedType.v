(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Lt Peano_dec Compare_dec EqNat
 Equalities Orders OrdersTac.


(** * DecidableType structure for Peano numbers *)

Module Nat_as_UBE <: UsualBoolEq.
 Definition t := nat.
 Definition eq := @eq nat.
 Definition eqb := beq_nat.
 Definition eqb_eq := beq_nat_true_iff.
End Nat_as_UBE.

Module Nat_as_DT <: UsualDecidableTypeFull := Make_UDTF Nat_as_UBE.

(** Note that the last module fulfills by subtyping many other
    interfaces, such as [DecidableType] or [EqualityType]. *)



(** * OrderedType structure for Peano numbers *)

Module Nat_as_OT <: OrderedTypeFull.
 Include Nat_as_DT.
 Definition lt := lt.
 Definition le := le.
 Definition compare := nat_compare.

 Instance lt_strorder : StrictOrder lt.
 Proof. split; [ exact lt_irrefl | exact lt_trans ]. Qed.

 Instance lt_compat : Proper (Logic.eq==>Logic.eq==>iff) lt.
 Proof. repeat red; intros; subst; auto. Qed.

 Definition le_lteq := le_lt_or_eq_iff.
 Definition compare_spec := nat_compare_spec.

End Nat_as_OT.

(** Note that [Nat_as_OT] can also be seen as a [UsualOrderedType]
   and a [OrderedType] (and also as a [DecidableType]). *)



(** * An [order] tactic for Peano numbers *)

Module NatOrder := OTF_to_OrderTac Nat_as_OT.
Ltac nat_order := NatOrder.order.

(** Note that [nat_order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)

Section Test.
Let test : forall x y : nat, x<=y -> y<=x -> x=y.
Proof. nat_order. Qed.
End Test.
