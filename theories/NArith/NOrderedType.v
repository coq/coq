(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinNat
 DecidableType2 OrderedType2 OrderedType2Facts.

Local Open Scope N_scope.

(** * DecidableType structure for [N] binary natural numbers *)

Module N_as_MiniDT <: MiniDecidableType.
 Definition t := N.
 Definition eq_dec := N_eq_dec.
End N_as_MiniDT.

Module N_as_DT <: UsualDecidableType := Make_UDT N_as_MiniDT.

(** Note that [N_as_DT] can also be seen as a [DecidableType]
    and a [DecidableTypeOrig]. *)



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

 Lemma le_lteq : forall x y, x <= y <-> x < y \/ x=y.
 Proof.
 unfold Nle, Nlt; intros. rewrite <- Ncompare_eq_correct.
 destruct (x ?= y); intuition; discriminate.
 Qed.

 Lemma compare_spec : forall x y, Cmp eq lt x y (Ncompare x y).
 Proof.
 intros.
 destruct (Ncompare x y) as [ ]_eqn; constructor; auto.
 apply Ncompare_Eq_eq; auto.
 apply Ngt_Nlt; auto.
 Qed.

End N_as_OT.

(* Note that [N_as_OT] can also be seen as a [UsualOrderedType]
   and a [OrderedType] (and also as a [DecidableType]). *)



(** * An [order] tactic for [N] numbers *)

Module NOrder := OTF_to_OrderTac N_as_OT.
Ltac n_order :=
 change (@eq N) with NOrder.OrderElts.eq in *;
 NOrder.order.

(** Note that [n_order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)

