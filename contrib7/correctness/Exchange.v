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

Require ProgInt.
Require Arrays.

Set Implicit Arguments.

(* Definition *)

Inductive exchange [n:Z; A:Set; t,t':(array n A); i,j:Z] : Prop :=
  exchange_c :
    `0<=i<n` -> `0<=j<n` ->
    (#t[i] = #t'[j]) ->
    (#t[j] = #t'[i]) ->
    ((k:Z)`0<=k<n` -> `k<>i` -> `k<>j` -> #t[k] = #t'[k]) ->
    (exchange t t' i j).
    
(* Properties about exchanges *)

Lemma exchange_1 : (n:Z)(A:Set)(t:(array n A))
  (i,j:Z) `0<=i<n` -> `0<=j<n` ->
  (access (store (store t i #t[j]) j #t[i]) i) = #t[j].
Proof.
Intros n A t i j H_i H_j.
Case (dec_eq j i).
Intro eq_i_j. Rewrite eq_i_j.
Auto with datatypes.
Intro not_j_i.
Rewrite (store_def_2 (store t i #t[j]) #t[i] H_j H_i not_j_i).
Auto with datatypes.
Save.

Hints Resolve exchange_1 : v62 datatypes.


Lemma exchange_proof :
  (n:Z)(A:Set)(t:(array n A))
  (i,j:Z) `0<=i<n` -> `0<=j<n` ->
  (exchange (store (store t i (access t j)) j (access t i)) t i j).
Proof.
Intros n A t i j H_i H_j.
Apply exchange_c; Auto with datatypes.
Intros k H_k not_k_i not_k_j.
Cut ~j=k; Auto with datatypes. Intro not_j_k.
Rewrite (store_def_2 (store t i (access t j)) (access t i) H_j H_k not_j_k).
Auto with datatypes.
Save.

Hints Resolve exchange_proof : v62 datatypes.


Lemma exchange_sym :
  (n:Z)(A:Set)(t,t':(array n A))(i,j:Z)
  (exchange t t' i j) -> (exchange t' t i j).
Proof.
Intros n A t t' i j H1.
Elim H1. Clear H1. Intros.
Constructor 1; Auto with datatypes.
Intros. Rewrite (H3 k); Auto with datatypes.
Save.

Hints Resolve exchange_sym : v62 datatypes.


Lemma exchange_id :
  (n:Z)(A:Set)(t,t':(array n A))(i,j:Z)
  (exchange t t' i j) -> 
  i=j ->
  (k:Z) `0 <= k < n` -> (access t k)=(access t' k).
Proof.
Intros n A t t' i j Hex Heq k Hk.
Elim Hex. Clear Hex. Intros.
Rewrite Heq in H1. Rewrite Heq in H2.
Case (Z_eq_dec k j). 
  Intro Heq'. Rewrite Heq'. Assumption.
  Intro Hnoteq. Apply (H3 k); Auto with datatypes. Rewrite Heq. Assumption.
Save.

Hints Resolve exchange_id : v62 datatypes.
