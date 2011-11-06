(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

Require Import ZArith.
Require Import Coq.Arith.Max.
Require Import List.
Set Implicit Arguments.

(* I have addded a Leaf constructor to the varmap data structure (/plugins/ring/Quote.v)
   -- this is harmless and spares a lot of Empty.
   This means smaller proof-terms.
   BTW, by dropping the  polymorphism, I get small (yet noticeable) speed-up.
*)

Section S.

  Variable D :Type.

  Definition Env := positive -> D.

  Definition jump  (j:positive) (e:Env) := fun x => e (Pplus x j).

  Definition nth  (n:positive) (e : Env ) := e n.

  Definition hd (x:D)  (e: Env)  := nth xH e.

  Definition tail (e: Env) := jump xH e.

  Lemma psucc : forall p,  (match p with
                              | xI y' => xO (Psucc y')
                              | xO y' => xI y'
                              | 1%positive => 2%positive
                            end) = (p+1)%positive.
  Proof.
    destruct p.
    auto with zarith.
    rewrite xI_succ_xO.
    auto with zarith.
    reflexivity.
  Qed.

  Lemma jump_Pplus : forall i j l,
    forall x, jump (i + j) l x = jump i (jump j l) x.
  Proof.
    unfold jump.
    intros.
    rewrite Pplus_assoc.
    reflexivity.
  Qed.

  Lemma jump_simpl : forall p l,
    forall x, jump p l x =
    match p with
      | xH => tail l x
      | xO p => jump p (jump p l) x
      | xI p  => jump p (jump p (tail l)) x
    end.
  Proof.
    destruct p ; unfold tail ; intros ;  repeat rewrite <- jump_Pplus.
    (* xI p = p + p + 1 *)
    rewrite xI_succ_xO.
    rewrite Pplus_diag.
    rewrite <- Pplus_one_succ_r.
    reflexivity.
    (* xO p = p + p *)
    rewrite Pplus_diag.
    reflexivity.
    reflexivity.
  Qed.

  Ltac jump_s :=
    repeat
      match goal with
        | |- context [jump xH ?e] => rewrite (jump_simpl xH)
        | |- context [jump (xO ?p) ?e] => rewrite (jump_simpl (xO p))
        | |- context [jump (xI ?p) ?e] => rewrite (jump_simpl (xI p))
      end.

  Lemma jump_tl : forall j l, forall x, tail (jump j l) x = jump j (tail l) x.
  Proof.
    unfold tail.
    intros.
    repeat rewrite <- jump_Pplus.
    rewrite Pplus_comm.
    reflexivity.
  Qed.

  Lemma jump_Psucc : forall j l,
    forall x, (jump (Psucc j) l x) = (jump 1 (jump j l) x).
  Proof.
    intros.
    rewrite <- jump_Pplus.
    rewrite Pplus_one_succ_r.
    rewrite Pplus_comm.
    reflexivity.
  Qed.

  Lemma jump_Pdouble_minus_one : forall i l,
    forall x, (jump (Pdouble_minus_one i) (tail l)) x = (jump i (jump i l)) x.
  Proof.
    unfold tail.
    intros.
    repeat rewrite <- jump_Pplus.
    rewrite <- Pplus_one_succ_r.
    rewrite Psucc_o_double_minus_one_eq_xO.
    rewrite Pplus_diag.
    reflexivity.
  Qed.

  Lemma jump_x0_tail : forall p l, forall x, jump (xO p) (tail l) x = jump (xI p) l x.
  Proof.
    intros.
    unfold jump.
    unfold tail.
    unfold jump.
    rewrite <- Pplus_assoc.
    simpl.
    reflexivity.
  Qed.

  Lemma nth_spec : forall p l x,
    nth p l =
    match p with
      | xH => hd x l
      | xO p => nth p (jump p l)
      | xI p => nth p (jump p (tail l))
    end.
  Proof.
    unfold nth.
    destruct p.
    intros.
    unfold jump, tail.
    unfold jump.
    rewrite Pplus_diag.
    rewrite xI_succ_xO.
    simpl.
    reflexivity.
    unfold jump.
    rewrite Pplus_diag.
    reflexivity.
    unfold hd.
    unfold nth.
    reflexivity.
  Qed.


  Lemma nth_jump : forall p l x, nth p (tail l) = hd x (jump p l).
  Proof.
    unfold tail.
    unfold hd.
    unfold jump.
    unfold nth.
    intros.
    rewrite Pplus_comm.
    reflexivity.
  Qed.

  Lemma nth_Pdouble_minus_one :
    forall p l, nth (Pdouble_minus_one p) (tail l) = nth p (jump p l).
  Proof.
    intros.
    unfold tail.
    unfold nth, jump.
    rewrite Pplus_diag.
    rewrite <- Psucc_o_double_minus_one_eq_xO.
    rewrite Pplus_one_succ_r.
    reflexivity.
  Qed.

End S.

