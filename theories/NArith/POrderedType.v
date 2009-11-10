(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinPos
 DecidableType2 OrderedType2 OrderedType2Facts.

Local Open Scope positive_scope.

(** * DecidableType structure for [positive] numbers *)

Module Positive_as_MiniDT <: MiniDecidableType.
 Definition t := positive.
 Definition eq_dec := positive_eq_dec.
End Positive_as_MiniDT.

Module Positive_as_DT <: UsualDecidableType.
 Include Make_UDT Positive_as_MiniDT.
 Definition eqb := Peqb.
 Definition eqb_eq := Peqb_eq.
End Positive_as_DT.


(** Note that [Positive_as_DT] can also be seen as a [DecidableType]
    and a [DecidableTypeOrig] and a [BooleanEqualityType]. *)



(** * OrderedType structure for [positive] numbers *)

Module Positive_as_OT <: OrderedTypeFull.
 Include Positive_as_DT.
 Definition lt := Plt.
 Definition le := Ple.
 Definition compare p q := Pcompare p q Eq.

 Instance lt_strorder : StrictOrder Plt.
 Proof. split; [ exact Plt_irrefl | exact Plt_trans ]. Qed.

 Instance lt_compat : Proper (Logic.eq==>Logic.eq==>iff) Plt.
 Proof. repeat red; intros; subst; auto. Qed.

 Definition le_lteq := Ple_lteq.
 Definition compare_spec := Pcompare_spec.

End Positive_as_OT.

(** Note that [Positive_as_OT] can also be seen as a [UsualOrderedType]
   and a [OrderedType] (and also as a [DecidableType]). *)



(** * An [order] tactic for positive numbers *)

Module PositiveOrder := OTF_to_OrderTac Positive_as_OT.
Ltac p_order :=
 change (@eq positive) with PositiveOrder.OrderElts.eq in *;
 PositiveOrder.order.

(** Note that [p_order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)
