(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import List.
Require Import Multiset.
Require Import Permutation.
Require Import Relations.

Set Implicit Arguments.

Section defs.

  Variable A : Type.
  Variable leA : relation A.
  Variable eqA : relation A.

  Let gtA (x y:A) := ~ leA x y.
  
  Hypothesis leA_dec : forall x y:A, {leA x y} + {leA y x}.
  Hypothesis eqA_dec : forall x y:A, {eqA x y} + {~ eqA x y}.
  Hypothesis leA_refl : forall x y:A, eqA x y -> leA x y.
  Hypothesis leA_trans : forall x y z:A, leA x y -> leA y z -> leA x z.
  Hypothesis leA_antisym : forall x y:A, leA x y -> leA y x -> eqA x y.

  Hint Resolve leA_refl.
  Hint Immediate eqA_dec leA_dec leA_antisym.

  Let emptyBag := EmptyBag A.
  Let singletonBag := SingletonBag _ eqA_dec.

  (** [lelistA] *)

  Inductive lelistA (a:A) : list A -> Prop :=
    | nil_leA : lelistA a nil
    | cons_leA : forall (b:A) (l:list A), leA a b -> lelistA a (b :: l).

  Lemma lelistA_inv : forall (a b:A) (l:list A), lelistA a (b :: l) -> leA a b.
  Proof.
    intros; inversion H; trivial with datatypes.
  Qed.

  (** * Definition for a list to be sorted *)

  Inductive sort : list A -> Prop :=
    | nil_sort : sort nil
    | cons_sort :
      forall (a:A) (l:list A), sort l -> lelistA a l -> sort (a :: l).

  Lemma sort_inv :
    forall (a:A) (l:list A), sort (a :: l) -> sort l /\ lelistA a l.
  Proof.
    intros; inversion H; auto with datatypes.
  Qed.

  Lemma sort_rect :
    forall P:list A -> Type,
      P nil ->
      (forall (a:A) (l:list A), sort l -> P l -> lelistA a l -> P (a :: l)) ->
      forall y:list A, sort y -> P y.
  Proof.
    simple induction y; auto with datatypes.
    intros; elim (sort_inv (a:=a) (l:=l)); auto with datatypes.
  Qed.

  Lemma sort_rec :
    forall P:list A -> Set,
      P nil ->
      (forall (a:A) (l:list A), sort l -> P l -> lelistA a l -> P (a :: l)) ->
      forall y:list A, sort y -> P y.
  Proof.
    simple induction y; auto with datatypes.
    intros; elim (sort_inv (a:=a) (l:=l)); auto with datatypes.
  Qed.

  (** * Merging two sorted lists *)

  Inductive merge_lem (l1 l2:list A) : Type :=
    merge_exist :
    forall l:list A,
      sort l ->
      meq (list_contents _ eqA_dec l)
      (munion (list_contents _ eqA_dec l1) (list_contents _ eqA_dec l2)) ->
      (forall a:A, lelistA a l1 -> lelistA a l2 -> lelistA a l) ->
      merge_lem l1 l2.

  Lemma merge :
    forall l1:list A, sort l1 -> forall l2:list A, sort l2 -> merge_lem l1 l2.
  Proof.
    simple induction 1; intros.
    apply merge_exist with l2; auto with datatypes.
    elim H2; intros.
    apply merge_exist with (a :: l); simpl in |- *; auto using cons_sort with datatypes.
    elim (leA_dec a a0); intros.

    (* 1 (leA a a0) *)
    cut (merge_lem l (a0 :: l0)); auto using cons_sort with datatypes.
    intros [l3 l3sorted l3contents Hrec].
    apply merge_exist with (a :: l3); simpl in |- *;
      auto using cons_sort, cons_leA with datatypes.
    apply meq_trans with
      (munion (singletonBag a)
	(munion (list_contents _ eqA_dec l)
          (list_contents _ eqA_dec (a0 :: l0)))).
    apply meq_right; trivial with datatypes.
    apply meq_sym; apply munion_ass.
    intros; apply cons_leA.
    apply lelistA_inv with l; trivial with datatypes.

    (* 2 (leA a0 a) *)
    elim X0; simpl in |- *; intros.
    apply merge_exist with (a0 :: l3); simpl in |- *; 
      auto using cons_sort, cons_leA with datatypes.
    apply meq_trans with
      (munion (singletonBag a0)
	(munion (munion (singletonBag a) (list_contents _ eqA_dec l))
          (list_contents _ eqA_dec l0))).
    apply meq_right; trivial with datatypes.
    apply munion_perm_left.
    intros; apply cons_leA; apply lelistA_inv with l0; trivial with datatypes.
  Qed.

End defs.

Unset Implicit Arguments.
Hint Constructors sort: datatypes v62.
Hint Constructors lelistA: datatypes v62.
