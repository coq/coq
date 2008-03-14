(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

(****************************************************************************)
(*                   Exchange of two elements in an array                   *)
(*                        Definition and properties                         *)
(****************************************************************************)

Require Import ProgInt.
Require Import Arrays.

Set Implicit Arguments.

(* Definition *)

Inductive exchange (n:Z) (A:Set) (t t':array n A) (i j:Z) : Prop :=
    exchange_c :
      (0 <= i < n)%Z ->
      (0 <= j < n)%Z ->
      #t [i] = #t' [j] ->
      #t [j] = #t' [i] ->
      (forall k:Z, (0 <= k < n)%Z -> k <> i -> k <> j -> #t [k] = #t' [k]) ->
      exchange t t' i j.
    
(* Properties about exchanges *)

Lemma exchange_1 :
 forall (n:Z) (A:Set) (t:array n A) (i j:Z),
   (0 <= i < n)%Z ->
   (0 <= j < n)%Z -> #(store (store t i #t [j]) j #t [i]) [i] = #t [j].
Proof.
intros n A t i j H_i H_j.
case (dec_eq j i).
intro eq_i_j. rewrite eq_i_j.
auto with datatypes.
intro not_j_i.
rewrite (store_def_2 (store t i #t [j]) #t [i] H_j H_i not_j_i).
auto with datatypes.
Qed.

Hint Resolve exchange_1: v62 datatypes.


Lemma exchange_proof :
 forall (n:Z) (A:Set) (t:array n A) (i j:Z),
   (0 <= i < n)%Z ->
   (0 <= j < n)%Z -> exchange (store (store t i #t [j]) j #t [i]) t i j.
Proof.
intros n A t i j H_i H_j.
apply exchange_c; auto with datatypes.
intros k H_k not_k_i not_k_j.
cut (j <> k); auto with datatypes. intro not_j_k.
rewrite (store_def_2 (store t i #t [j]) #t [i] H_j H_k not_j_k).
auto with datatypes.
Qed.

Hint Resolve exchange_proof: v62 datatypes.


Lemma exchange_sym :
 forall (n:Z) (A:Set) (t t':array n A) (i j:Z),
   exchange t t' i j -> exchange t' t i j.
Proof.
intros n A t t' i j H1.
elim H1. clear H1. intros.
constructor 1; auto with datatypes.
intros. rewrite (H3 k); auto with datatypes.
Qed.

Hint Resolve exchange_sym: v62 datatypes.


Lemma exchange_id :
 forall (n:Z) (A:Set) (t t':array n A) (i j:Z),
   exchange t t' i j ->
   i = j -> forall k:Z, (0 <= k < n)%Z -> #t [k] = #t' [k].
Proof.
intros n A t t' i j Hex Heq k Hk.
elim Hex. clear Hex. intros.
rewrite Heq in H1. rewrite Heq in H2.
case (Z_eq_dec k j). 
  intro Heq'. rewrite Heq'. assumption.
  intro Hnoteq. apply (H3 k); auto with datatypes. rewrite Heq. assumption.
Qed.

Hint Resolve exchange_id: v62 datatypes.