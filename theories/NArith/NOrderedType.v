(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinNat Equalities Orders OrdersTac.

Local Open Scope N_scope.

(** * DecidableType structure for [N] binary natural numbers *)

Module N_as_UBE <: UsualBoolEq.
 Definition t := N.
 Definition eq := @eq N.
 Definition eqb := Neqb.
 Definition eqb_eq := Neqb_eq.
End N_as_UBE.

Module N_as_DT <: UsualDecidableTypeFull := Make_UDTF N_as_UBE.

(** Note that the last module fulfills by subtyping many other
    interfaces, such as [DecidableType] or [EqualityType]. *)



(** * OrderedType structure for [N] numbers *)

Module N_as_OT <: OrderedTypeFull.
 Include N_as_DT.
 Definition lt := Nlt.
 Definition le := Nle.
 Definition compare := Ncompare.

 Instance lt_strorder : StrictOrder Nlt.
 Proof. split; [ exact Nlt_irrefl | exact Nlt_trans ]. Qed.

 Instance lt_compat : Proper (Logic.eq==>Logic.eq==>iff) Nlt.
 Proof. repeat red; intros; subst; auto. Qed.

 Definition le_lteq := Nle_lteq.
 Definition compare_spec := Ncompare_spec.

End N_as_OT.

(** Note that [N_as_OT] can also be seen as a [UsualOrderedType]
   and a [OrderedType] (and also as a [DecidableType]). *)



(** * An [order] tactic for [N] numbers *)

Module NOrder := OTF_to_OrderTac N_as_OT.
Ltac n_order := NOrder.order.

(** Note that [n_order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)

