(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Library for binary natural numbers *)

Require Export BinNums.
Require Export BinPos.
Require Export BinNat.
Require Export Nnat.
Require Export Ndiv_def.
Require Export Nsqrt_def.
Require Export Ngcd_def.
Require Export Ndigits.
Require Export NArithRing.

(** [N] contains an [order] tactic for natural numbers *)

(** Note that [N.order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)

Local Open Scope N_scope.

Section TestOrder.
 Let test : forall x y, x<=y -> y<=x -> x=y.
 Proof.
 N.order.
 Qed.
End TestOrder.
