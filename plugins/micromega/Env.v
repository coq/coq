(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

Require Import BinInt List.
Set Implicit Arguments.
Local Open Scope positive_scope.

Section S.

  Variable D :Type.

  Definition Env := positive -> D.

  Definition jump (j:positive) (e:Env) := fun x => e (x+j).

  Definition nth (n:positive) (e:Env) := e n.

  Definition hd (e:Env) := nth 1 e.

  Definition tail (e:Env) := jump 1 e.

  Lemma jump_add i j l x : jump (i + j) l x = jump i (jump j l) x.
  Proof.
    unfold jump. f_equal. apply Pos.add_assoc.
  Qed.

  Lemma jump_simpl p l x :
    jump p l x =
    match p with
      | xH => tail l x
      | xO p => jump p (jump p l) x
      | xI p  => jump p (jump p (tail l)) x
    end.
  Proof.
    destruct p; unfold tail; rewrite <- ?jump_add; f_equal;
    now rewrite Pos.add_diag.
  Qed.

  Lemma jump_tl j l x : tail (jump j l) x = jump j (tail l) x.
  Proof.
    unfold tail. rewrite <- !jump_add. f_equal. apply Pos.add_comm.
  Qed.

  Lemma jump_succ j l x : jump (Pos.succ j) l x = jump 1 (jump j l) x.
  Proof.
    rewrite <- jump_add. f_equal. symmetry. apply Pos.add_1_l.
  Qed.

  Lemma jump_pred_double i l x :
    jump (Pos.pred_double i) (tail l) x = jump i (jump i l) x.
  Proof.
    unfold tail. rewrite <- !jump_add. f_equal.
    now rewrite Pos.add_1_r, Pos.succ_pred_double, Pos.add_diag.
  Qed.

  Lemma nth_spec p l :
    nth p l =
    match p with
      | xH => hd l
      | xO p => nth p (jump p l)
      | xI p => nth p (jump p (tail l))
    end.
  Proof.
    unfold hd, nth, tail, jump.
    destruct p; f_equal; now rewrite Pos.add_diag.
  Qed.

  Lemma nth_jump p l : nth p (tail l) = hd (jump p l).
  Proof.
    unfold hd, nth, tail, jump. f_equal. apply Pos.add_comm.
  Qed.

  Lemma nth_pred_double p l :
    nth (Pos.pred_double p) (tail l) = nth p (jump p l).
  Proof.
    unfold nth, tail, jump. f_equal.
    now rewrite Pos.add_1_r, Pos.succ_pred_double, Pos.add_diag.
  Qed.

End S.

Ltac jump_simpl :=
  repeat
    match goal with
      | |- context [jump xH] => rewrite (jump_simpl xH)
      | |- context [jump (xO ?p)] => rewrite (jump_simpl (xO p))
      | |- context [jump (xI ?p)] => rewrite (jump_simpl (xI p))
    end.
