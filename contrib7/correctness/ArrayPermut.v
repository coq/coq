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
(*                    Permutations of elements in arrays                    *)
(*                        Definition and properties                         *)
(****************************************************************************)

Require ProgInt.
Require Arrays.
Require Export Exchange.

Require Omega.

Set Implicit Arguments.

(* We define "permut" as the smallest equivalence relation which contains
 * transpositions i.e. exchange of two elements.
 *)

Inductive permut [n:Z; A:Set] : (array n A)->(array n A)->Prop :=
    exchange_is_permut : 
      (t,t':(array n A))(i,j:Z)(exchange t t' i j) -> (permut t t')
  | permut_refl : 
      (t:(array n A))(permut t t)
  | permut_sym : 
      (t,t':(array n A))(permut t t') -> (permut t' t)
  | permut_trans : 
      (t,t',t'':(array n A))
      (permut t t') -> (permut t' t'') -> (permut t t'').

Hints Resolve exchange_is_permut permut_refl permut_sym permut_trans : v62 datatypes.

(* We also define the permutation on a segment of an array, "sub_permut",
 * the other parts of the array being unchanged
 *
 * One again we define it as the smallest equivalence relation containing
 * transpositions on the given segment.
 *)

Inductive sub_permut [n:Z; A:Set; g,d:Z] : (array n A)->(array n A)->Prop :=
    exchange_is_sub_permut : 
      (t,t':(array n A))(i,j:Z)`g <= i <= d` -> `g <= j <= d`
      -> (exchange t t' i j) -> (sub_permut g d t t')
  | sub_permut_refl : 
      (t:(array n A))(sub_permut g d t t)
  | sub_permut_sym : 
      (t,t':(array n A))(sub_permut g d t t') -> (sub_permut g d t' t)
  | sub_permut_trans : 
      (t,t',t'':(array n A))
      (sub_permut g d t t') -> (sub_permut g d t' t'') 
      -> (sub_permut g d t t'').

Hints Resolve exchange_is_sub_permut sub_permut_refl sub_permut_sym sub_permut_trans
  : v62 datatypes.

(* To express that some parts of arrays are equal we introduce the
 * property "array_id" which says that a segment is the same on two
 * arrays.
 *)

Definition array_id := [n:Z][A:Set][t,t':(array n A)][g,d:Z]
  (i:Z) `g <= i <= d` -> #t[i] = #t'[i].

(* array_id is an equivalence relation *)

Lemma array_id_refl : 
  (n:Z)(A:Set)(t:(array n A))(g,d:Z)
  (array_id t t g d).
Proof.
Unfold array_id.
Auto with datatypes.
Save.

Hints Resolve array_id_refl : v62 datatypes.

Lemma array_id_sym :
  (n:Z)(A:Set)(t,t':(array n A))(g,d:Z)
  (array_id t t' g d)
  -> (array_id t' t g d).
Proof.
Unfold array_id. Intros.
Symmetry; Auto with datatypes.
Save.

Hints Resolve  array_id_sym : v62 datatypes.

Lemma array_id_trans :
  (n:Z)(A:Set)(t,t',t'':(array n A))(g,d:Z)
  (array_id t t' g d)
  -> (array_id t' t'' g d)
    -> (array_id t t'' g d).
Proof.
Unfold array_id. Intros.
Apply trans_eq with y:=#t'[i]; Auto with datatypes.
Save.

Hints Resolve array_id_trans: v62 datatypes.

(* Outside the segment [g,d] the elements are equal *)

Lemma sub_permut_id :
  (n:Z)(A:Set)(t,t':(array n A))(g,d:Z)
  (sub_permut g d t t') ->
  (array_id t t' `0` `g-1`) /\ (array_id t t' `d+1` `n-1`).
Proof.
Intros n A t t' g d. Induction 1; Intros.
Elim H2; Intros.
Unfold array_id; Split; Intros.
Apply H7; Omega.
Apply H7; Omega.
Auto with datatypes.
Decompose [and] H1; Auto with datatypes.
Decompose [and] H1; Decompose [and] H3; EAuto with datatypes.
Save.

Hints Resolve sub_permut_id.

Lemma sub_permut_eq :
  (n:Z)(A:Set)(t,t':(array n A))(g,d:Z)
  (sub_permut g d t t') ->
  (i:Z) (`0<=i<g` \/ `d<i<n`) -> #t[i]=#t'[i].
Proof.
Intros n A t t' g d Htt' i Hi.
Elim (sub_permut_id Htt'). Unfold array_id. 
Intros.
Elim Hi; [ Intro; Apply H; Omega | Intro; Apply H0; Omega ].
Save.

(* sub_permut is a particular case of permutation *)

Lemma sub_permut_is_permut :
  (n:Z)(A:Set)(t,t':(array n A))(g,d:Z)
  (sub_permut g d t t') ->
  (permut t t').
Proof.
Intros n A t t' g d. Induction 1; Intros; EAuto with datatypes.
Save.

Hints Resolve sub_permut_is_permut.

(* If we have a sub-permutation on an empty segment, then we have a 
 * sub-permutation on any segment.
 *)

Lemma sub_permut_void :
  (N:Z)(A:Set)(t,t':(array N A))
  (g,g',d,d':Z) `d < g`
   -> (sub_permut g d t t') -> (sub_permut g' d' t t').
Proof.
Intros N A t t' g g' d d' Hdg.
(Induction 1; Intros).
(Absurd `g <= d`; Omega).
Auto with datatypes.
Auto with datatypes.
EAuto with datatypes.
Save.

(* A sub-permutation on a segment may be extended to any segment that
 * contains the first one.
 *)

Lemma sub_permut_extension :
  (N:Z)(A:Set)(t,t':(array N A))
  (g,g',d,d':Z) `g' <= g` -> `d <= d'`
   -> (sub_permut g d t t') -> (sub_permut g' d' t t').
Proof.
Intros N A t t' g g' d d' Hgg' Hdd'.
(Induction 1; Intros).
Apply exchange_is_sub_permut with i:=i j:=j; [ Omega | Omega | Assumption ].
Auto with datatypes.
Auto with datatypes.
EAuto with datatypes.
Save.
