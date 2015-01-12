(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinPos Equalities Orders OrdersTac.

Local Open Scope positive_scope.

(** * DecidableType structure for [positive] numbers *)

Module Positive_as_DT <: UsualDecidableTypeFull := Pos.

(** Note that the last module fulfills by subtyping many other
    interfaces, such as [DecidableType] or [EqualityType]. *)


(** * OrderedType structure for [positive] numbers *)

Module Positive_as_OT <: OrderedTypeFull := Pos.

(** Note that [Positive_as_OT] can also be seen as a [UsualOrderedType]
   and a [OrderedType] (and also as a [DecidableType]). *)



(** * An [order] tactic for positive numbers *)

Module PositiveOrder := OTF_to_OrderTac Positive_as_OT.
Ltac p_order := PositiveOrder.order.

(** Note that [p_order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)
