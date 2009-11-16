(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinInt Zcompare Zorder Zbool ZArith_dec
 DecidableType2 OrderedType2 OrderedType2Facts.

Local Open Scope Z_scope.

(** * DecidableType structure for binary integers *)

Module Z_as_UBE <: UsualBoolEq.
 Definition t := Z.
 Definition eq := @eq Z.
 Definition eqb := Zeq_bool.
 Definition eqb_eq x y := iff_sym (Zeq_is_eq_bool x y).
End Z_as_UBE.

Module Z_as_DT <: UsualDecidableTypeFull := Make_UDTF Z_as_UBE.

(** Note that the last module fulfills by subtyping many other
    interfaces, such as [DecidableType] or [EqualityType]. *)


(** * OrderedType structure for binary integers *)

Module Z_as_OT <: OrderedTypeFull.
 Include Z_as_DT.
 Definition lt := Zlt.
 Definition le := Zle.
 Definition compare := Zcompare.

 Instance lt_strorder : StrictOrder Zlt.
 Proof. split; [ exact Zlt_irrefl | exact Zlt_trans ]. Qed.

 Instance lt_compat : Proper (Logic.eq==>Logic.eq==>iff) Zlt.
 Proof. repeat red; intros; subst; auto. Qed.

 Definition le_lteq := Zle_lt_or_eq_iff.
 Definition compare_spec := Zcompare_spec.

End Z_as_OT.

(** Note that [Z_as_OT] can also be seen as a [UsualOrderedType]
   and a [OrderedType] (and also as a [DecidableType]). *)



(** * An [order] tactic for integers *)

Module ZOrder := OTF_to_OrderTac Z_as_OT.
Ltac z_order :=
 change (@eq Z) with ZOrder.OrderElts.eq in *;
 ZOrder.order.

(** Note that [z_order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)

