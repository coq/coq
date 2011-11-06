(* -*- coding: utf-8 -*- *)
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

Section MakeVarMap.
  Variable A : Type.
  Variable default : A.

  Inductive t  : Type :=
  | Empty : t
  | Leaf : A -> t
  | Node : t  -> A -> t  -> t .

  Fixpoint find   (vm : t ) (p:positive) {struct vm} : A :=
    match vm with
      | Empty => default
      | Leaf i => i
      | Node l e r => match p with
                        | xH => e
                        | xO p => find l p
                        | xI p => find r p
                      end
    end.

 (* an off_map (a map with offset) offers the same functionalites  as /plugins/setoid_ring/BinList.v - it is used in EnvRing.v *)
(*
  Definition off_map  :=  (option positive *t )%type.



  Definition jump  (j:positive) (l:off_map ) :=
    let (o,m) := l in
      match o with
        | None => (Some j,m)
        | Some j0 => (Some (j+j0)%positive,m)
      end.

  Definition nth  (n:positive) (l: off_map ) :=
    let (o,m) := l in
      let idx  := match o with
                    | None => n
                    | Some i => i + n
                  end%positive in
      find  idx m.


  Definition hd  (l:off_map) := nth  xH l.


  Definition tail (l:off_map ) := jump xH l.


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
    (jump (i + j) l) = (jump i (jump j l)).
  Proof.
    unfold jump.
    destruct l.
    destruct o.
    rewrite Pplus_assoc.
    reflexivity.
    reflexivity.
  Qed.

  Lemma jump_simpl : forall p l,
    jump p l =
    match p with
      | xH => tail l
      | xO p => jump p (jump p l)
      | xI p  => jump p (jump p (tail l))
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

  Lemma jump_tl : forall j l, tail (jump j l) = jump j (tail l).
  Proof.
    unfold tail.
    intros.
    repeat rewrite <- jump_Pplus.
    rewrite Pplus_comm.
    reflexivity.
  Qed.

  Lemma jump_Psucc : forall j l,
    (jump (Psucc j) l) = (jump 1 (jump j l)).
  Proof.
    intros.
    rewrite <- jump_Pplus.
    rewrite Pplus_one_succ_r.
    rewrite Pplus_comm.
    reflexivity.
  Qed.

  Lemma jump_Pdouble_minus_one : forall i l,
    (jump (Pdouble_minus_one i) (tail l)) = (jump i (jump i l)).
  Proof.
    unfold tail.
    intros.
    repeat rewrite <- jump_Pplus.
    rewrite <- Pplus_one_succ_r.
    rewrite Psucc_o_double_minus_one_eq_xO.
    rewrite Pplus_diag.
    reflexivity.
  Qed.

  Lemma jump_x0_tail : forall p l, jump (xO p) (tail l) = jump (xI p) l.
  Proof.
    intros.
    jump_s.
    repeat rewrite <- jump_Pplus.
    reflexivity.
  Qed.


  Lemma nth_spec : forall p l,
    nth p l =
    match p with
      | xH => hd  l
      | xO p => nth p (jump p l)
      | xI p => nth p (jump p (tail l))
    end.
  Proof.
    unfold nth.
    destruct l.
    destruct o.
    simpl.
    rewrite psucc.
    destruct p.
    replace (p0 + xI p)%positive with ((p + (p0 + 1) + p))%positive.
    reflexivity.
    rewrite xI_succ_xO.
    rewrite Pplus_one_succ_r.
    rewrite <- Pplus_diag.
    rewrite Pplus_comm.
    symmetry.
    rewrite (Pplus_comm p0).
    rewrite <- Pplus_assoc.
    rewrite (Pplus_comm 1)%positive.
    rewrite <- Pplus_assoc.
    reflexivity.
  (**)
    replace ((p0 + xO p))%positive with (p + p0 + p)%positive.
    reflexivity.
    rewrite <- Pplus_diag.
    rewrite <- Pplus_assoc.
    rewrite Pplus_comm.
    rewrite Pplus_assoc.
    reflexivity.
    reflexivity.
    simpl.
    destruct p.
    rewrite xI_succ_xO.
    rewrite Pplus_one_succ_r.
    rewrite <- Pplus_diag.
    symmetry.
    rewrite Pplus_comm.
    rewrite Pplus_assoc.
    reflexivity.
    rewrite Pplus_diag.
    reflexivity.
    reflexivity.
  Qed.


  Lemma nth_jump : forall p l, nth p (tail l) = hd (jump p l).
  Proof.
    destruct l.
    unfold tail.
    unfold hd.
    unfold jump.
    unfold nth.
    destruct o.
    symmetry.
    rewrite Pplus_comm.
    rewrite <- Pplus_assoc.
    rewrite (Pplus_comm p0).
    reflexivity.
    rewrite Pplus_comm.
    reflexivity.
  Qed.

  Lemma nth_Pdouble_minus_one :
    forall p l, nth (Pdouble_minus_one p) (tail l) = nth p (jump p l).
  Proof.
    destruct l.
    unfold tail.
    unfold nth, jump.
    destruct o.
    rewrite ((Pplus_comm p)).
    rewrite <- (Pplus_assoc p0).
    rewrite Pplus_diag.
    rewrite <- Psucc_o_double_minus_one_eq_xO.
    rewrite Pplus_one_succ_r.
    rewrite (Pplus_comm (Pdouble_minus_one p)).
    rewrite Pplus_assoc.
    rewrite (Pplus_comm p0).
    reflexivity.
    rewrite <- Pplus_one_succ_l.
    rewrite Psucc_o_double_minus_one_eq_xO.
    rewrite Pplus_diag.
    reflexivity.
  Qed.

*)

End MakeVarMap.

