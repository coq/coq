(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import BinPos.
Require Export List.
Set Implicit Arguments.
Local Open Scope positive_scope.

Section MakeBinList.
 Variable A : Type.
 Variable default : A.

 Fixpoint jump (p:positive) (l:list A) {struct p} : list A :=
  match p with
  | xH => tl l
  | xO p => jump p (jump p l)
  | xI p  => jump p (jump p (tl l))
  end.

 Fixpoint nth (p:positive) (l:list A) {struct p} : A:=
  match p with
  | xH => hd default l
  | xO p => nth p (jump p l)
  | xI p => nth p (jump p (tl l))
  end.

 Lemma jump_tl : forall j l, tl (jump j l) = jump j (tl l).
 Proof.
  induction j;simpl;intros; now rewrite ?IHj.
 Qed.

 Lemma jump_succ : forall j l,
  jump (Pos.succ j) l = jump 1 (jump j l).
 Proof.
  induction j;simpl;intros.
  - rewrite !IHj; simpl; now rewrite !jump_tl.
  - now rewrite !jump_tl.
  - trivial.
 Qed.

 Lemma jump_add : forall i j l,
  jump (i + j) l = jump i (jump j l).
 Proof.
  induction i using Pos.peano_ind; intros.
  - now rewrite Pos.add_1_l, jump_succ.
  - now rewrite Pos.add_succ_l, !jump_succ, IHi.
 Qed.

 Lemma jump_pred_double : forall i l,
  jump (Pos.pred_double i) (tl l) = jump i (jump i l).
 Proof.
  induction i;intros;simpl.
  - now rewrite !jump_tl.
  - now rewrite IHi, <- 2 jump_tl, IHi.
  - trivial.
 Qed.

 Lemma nth_jump : forall p l, nth p (tl l) = hd default (jump p l).
 Proof.
  induction p;simpl;intros.
  - now rewrite <-jump_tl, IHp.
  - now rewrite <-jump_tl, IHp.
  - trivial.
 Qed.

 Lemma nth_pred_double :
  forall p l, nth (Pos.pred_double p) (tl l) = nth p (jump p l).
 Proof.
  induction p;simpl;intros.
  - now rewrite !jump_tl.
  - now rewrite jump_pred_double, <- !jump_tl, IHp.
  - trivial.
 Qed.

End MakeBinList.
