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

Require Import ProgInt.
Require Import Arrays.
Require Export Exchange.

Require Import Omega.

Set Implicit Arguments.

(* We define "permut" as the smallest equivalence relation which contains
 * transpositions i.e. exchange of two elements.
 *)

Inductive permut (n:Z) (A:Set) : array n A -> array n A -> Prop :=
  | exchange_is_permut :
      forall (t t':array n A) (i j:Z), exchange t t' i j -> permut t t'
  | permut_refl : forall t:array n A, permut t t
  | permut_sym : forall t t':array n A, permut t t' -> permut t' t
  | permut_trans :
      forall t t' t'':array n A, permut t t' -> permut t' t'' -> permut t t''.

Hint Resolve exchange_is_permut permut_refl permut_sym permut_trans: v62
  datatypes.

(* We also define the permutation on a segment of an array, "sub_permut",
 * the other parts of the array being unchanged
 *
 * One again we define it as the smallest equivalence relation containing
 * transpositions on the given segment.
 *)

Inductive sub_permut (n:Z) (A:Set) (g d:Z) :
array n A -> array n A -> Prop :=
  | exchange_is_sub_permut :
      forall (t t':array n A) (i j:Z),
        (g <= i <= d)%Z ->
        (g <= j <= d)%Z -> exchange t t' i j -> sub_permut g d t t'
  | sub_permut_refl : forall t:array n A, sub_permut g d t t
  | sub_permut_sym :
      forall t t':array n A, sub_permut g d t t' -> sub_permut g d t' t
  | sub_permut_trans :
      forall t t' t'':array n A,
        sub_permut g d t t' -> sub_permut g d t' t'' -> sub_permut g d t t''.

Hint Resolve exchange_is_sub_permut sub_permut_refl sub_permut_sym
  sub_permut_trans: v62 datatypes.

(* To express that some parts of arrays are equal we introduce the
 * property "array_id" which says that a segment is the same on two
 * arrays.
 *)

Definition array_id (n:Z) (A:Set) (t t':array n A) 
  (g d:Z) := forall i:Z, (g <= i <= d)%Z -> #t [i] = #t' [i].

(* array_id is an equivalence relation *)

Lemma array_id_refl :
 forall (n:Z) (A:Set) (t:array n A) (g d:Z), array_id t t g d.
Proof.
unfold array_id in |- *.
auto with datatypes.
Qed.

Hint Resolve array_id_refl: v62 datatypes.

Lemma array_id_sym :
 forall (n:Z) (A:Set) (t t':array n A) (g d:Z),
   array_id t t' g d -> array_id t' t g d.
Proof.
unfold array_id in |- *. intros.
symmetry  in |- *; auto with datatypes.
Qed.

Hint Resolve array_id_sym: v62 datatypes.

Lemma array_id_trans :
 forall (n:Z) (A:Set) (t t' t'':array n A) (g d:Z),
   array_id t t' g d -> array_id t' t'' g d -> array_id t t'' g d.
Proof.
unfold array_id in |- *. intros.
apply trans_eq with (y := #t' [i]); auto with datatypes.
Qed.

Hint Resolve array_id_trans: v62 datatypes.

(* Outside the segment [g,d] the elements are equal *)

Lemma sub_permut_id :
 forall (n:Z) (A:Set) (t t':array n A) (g d:Z),
   sub_permut g d t t' ->
   array_id t t' 0 (g - 1) /\ array_id t t' (d + 1) (n - 1).
Proof.
intros n A t t' g d. simple induction 1; intros.
elim H2; intros.
unfold array_id in |- *; split; intros.
apply H7; omega.
apply H7; omega.
auto with datatypes.
decompose [and] H1; auto with datatypes.
decompose [and] H1; decompose [and] H3; eauto with datatypes.
Qed.

Hint Resolve sub_permut_id.

Lemma sub_permut_eq :
 forall (n:Z) (A:Set) (t t':array n A) (g d:Z),
   sub_permut g d t t' ->
   forall i:Z, (0 <= i < g)%Z \/ (d < i < n)%Z -> #t [i] = #t' [i].
Proof.
intros n A t t' g d Htt' i Hi.
elim (sub_permut_id Htt'). unfold array_id in |- *. 
intros.
elim Hi; [ intro; apply H; omega | intro; apply H0; omega ].
Qed.

(* sub_permut is a particular case of permutation *)

Lemma sub_permut_is_permut :
 forall (n:Z) (A:Set) (t t':array n A) (g d:Z),
   sub_permut g d t t' -> permut t t'.
Proof.
intros n A t t' g d. simple induction 1; intros; eauto with datatypes.
Qed.

Hint Resolve sub_permut_is_permut.

(* If we have a sub-permutation on an empty segment, then we have a 
 * sub-permutation on any segment.
 *)

Lemma sub_permut_void :
 forall (N:Z) (A:Set) (t t':array N A) (g g' d d':Z),
   (d < g)%Z -> sub_permut g d t t' -> sub_permut g' d' t t'.
Proof.
intros N A t t' g g' d d' Hdg.
simple induction 1; intros.
absurd (g <= d)%Z; omega.
auto with datatypes.
auto with datatypes.
eauto with datatypes.
Qed.

(* A sub-permutation on a segment may be extended to any segment that
 * contains the first one.
 *)

Lemma sub_permut_extension :
 forall (N:Z) (A:Set) (t t':array N A) (g g' d d':Z),
   (g' <= g)%Z -> (d <= d')%Z -> sub_permut g d t t' -> sub_permut g' d' t t'.
Proof.
intros N A t t' g g' d d' Hgg' Hdd'.
simple induction 1; intros.
apply exchange_is_sub_permut with (i := i) (j := j);
 [ omega | omega | assumption ].
auto with datatypes.
auto with datatypes.
eauto with datatypes.
Qed.