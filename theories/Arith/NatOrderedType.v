(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Lt Peano_dec Compare_dec EqNat
 DecidableType2 OrderedType2 OrderedType2Facts.


(** * DecidableType structure for Peano numbers *)

Module Nat_as_MiniDT <: MiniDecidableType.
 Definition t := nat.
 Definition eq_dec := eq_nat_dec.
End Nat_as_MiniDT.

Module Nat_as_DT <: UsualDecidableType.
 Include Make_UDT Nat_as_MiniDT.
 (** The next fields aren't mandatory but allow more subtyping. *)
 Definition eqb := beq_nat.
 Definition eqb_eq := beq_nat_true_iff.
End Nat_as_DT.

(** Note that [Nat_as_DT] can also be seen as a [DecidableType],
    or a [DecidableTypeOrig] or a [BooleanEqualityType]. *)



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
Ltac nat_order :=
 change (@eq nat) with NatOrder.OrderElts.eq in *;
 NatOrder.order.

(** Note that [nat_order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)

