(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Set Implicit Arguments.
Require Import BinPos.
Require Export List.
Require Export ListTactics.
Open Local Scope positive_scope.

Section MakeBinList.
 Variable A : Type.
 Variable default : A.

 Fixpoint jump (p:positive) (l:list A) {struct p} : list A :=
  match p with
  | xH => tail l
  | xO p => jump p (jump p l)
  | xI p  => jump p (jump p (tail l))
  end.

 Fixpoint nth (p:positive) (l:list A) {struct p} : A:=
  match p with
  | xH => hd default l
  | xO p => nth p (jump p l)
  | xI p => nth p (jump p (tail l))
  end.

 Lemma jump_tl : forall j l, tail (jump j l) = jump j (tail l).
 Proof.
  induction j;simpl;intros.
  repeat rewrite IHj;trivial.
  repeat rewrite IHj;trivial.
  trivial.
 Qed.

 Lemma jump_Psucc : forall j l,
  (jump (Psucc j) l) = (jump 1 (jump j l)).
 Proof.
  induction j;simpl;intros.
  repeat rewrite IHj;simpl;repeat rewrite jump_tl;trivial.
  repeat rewrite jump_tl;trivial.
  trivial.
 Qed.

 Lemma jump_Pplus : forall i j l,
  (jump (i + j) l) = (jump i (jump j l)).
 Proof.
  induction i;intros.
  rewrite xI_succ_xO;rewrite Pplus_one_succ_r.
  rewrite <- Pplus_diag;repeat rewrite <- Pplus_assoc.
  repeat rewrite IHi.
  rewrite Pplus_comm;rewrite <- Pplus_one_succ_r;rewrite jump_Psucc;trivial.
  rewrite <- Pplus_diag;repeat rewrite <- Pplus_assoc.
  repeat rewrite IHi;trivial.
  rewrite Pplus_comm;rewrite <- Pplus_one_succ_r;rewrite jump_Psucc;trivial.
 Qed.

 Lemma jump_Pdouble_minus_one : forall i l,
  (jump (Pdouble_minus_one i) (tail l)) = (jump i (jump i l)).
 Proof.
  induction i;intros;simpl.
  repeat rewrite jump_tl;trivial.
  rewrite IHi. do 2 rewrite <- jump_tl;rewrite IHi;trivial.
  trivial.
 Qed.


 Lemma nth_jump : forall p l, nth p (tail l) = hd default (jump p l).
 Proof.
  induction p;simpl;intros.
  rewrite <-jump_tl;rewrite IHp;trivial.
  rewrite <-jump_tl;rewrite IHp;trivial.
  trivial.
 Qed.

 Lemma nth_Pdouble_minus_one :
  forall p l, nth (Pdouble_minus_one p) (tail l) = nth p (jump p l).
 Proof.
  induction p;simpl;intros.
  repeat rewrite jump_tl;trivial.
  rewrite jump_Pdouble_minus_one.
  repeat rewrite <- jump_tl;rewrite IHp;trivial.
  trivial.
 Qed.

End MakeBinList.


