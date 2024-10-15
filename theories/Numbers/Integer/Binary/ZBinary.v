(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Attributes deprecated(since="8.20", note="Use Coq.ZArith.BinInt instead.").

Require Import ZAxioms ZProperties BinInt.

Local Open Scope Z_scope.

(** BinInt.Z is already implementing [ZAxiomsMiniSig] *)

Module Z
 <: ZAxiomsSig <: UsualOrderedTypeFull <: TotalOrder
 <: UsualDecidableTypeFull
 := BinInt.Z.

(** * An [order] tactic for integers *)

Ltac z_order := Z.order.

(** Note that [z_order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)

Section TestOrder.
 Let test : forall x y, x<=y -> y<=x -> x=y.
 Proof.
 z_order.
 Defined.
End TestOrder.

(** Z forms a ring *)

(*Lemma Zring : ring_theory 0 1 NZadd NZmul NZsub Z.opp NZeq.
Proof.
constructor.
exact Zadd_0_l.
exact Zadd_comm.
exact Zadd_assoc.
exact Zmul_1_l.
exact Zmul_comm.
exact Zmul_assoc.
exact Zmul_add_distr_r.
intros; now rewrite Zadd_opp_minus.
exact Zadd_opp_r.
Qed.

Add Ring ZR : Zring.*)
