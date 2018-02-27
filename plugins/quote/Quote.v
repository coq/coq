(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Declare ML Module "quote_plugin".

(***********************************************************************
  The "abstract" type index is defined to represent variables.

  index : Set
  index_eq : index -> bool
  index_eq_prop: (n,m:index)(index_eq n m)=true -> n=m
  index_lt : index -> bool
  varmap : Type -> Type.
  varmap_find : (A:Type)A -> index -> (varmap A) -> A.

  The first arg. of varmap_find is the default value to take
  if the object is not found in the varmap.

  index_lt defines a total well-founded order, but we don't prove that.

***********************************************************************)

Set Implicit Arguments.

Section variables_map.

Variable A : Type.

Inductive varmap : Type :=
  | Empty_vm : varmap
  | Node_vm : A -> varmap -> varmap -> varmap.

Inductive index : Set :=
  | Left_idx : index -> index
  | Right_idx : index -> index
  | End_idx : index.

Fixpoint varmap_find (default_value:A) (i:index) (v:varmap) {struct v} : A :=
  match i, v with
  | End_idx, Node_vm x _ _ => x
  | Right_idx i1, Node_vm x v1 v2 => varmap_find default_value i1 v2
  | Left_idx i1, Node_vm x v1 v2 => varmap_find default_value i1 v1
  | _, _ => default_value
  end.

Fixpoint index_eq (n m:index) {struct m} : bool :=
  match n, m with
  | End_idx, End_idx => true
  | Left_idx n', Left_idx m' => index_eq n' m'
  | Right_idx n', Right_idx m' => index_eq n' m'
  | _, _ => false
  end.

Fixpoint index_lt (n m:index) {struct m} : bool :=
  match n, m with
  | End_idx, Left_idx _ => true
  | End_idx, Right_idx _ => true
  | Left_idx n', Right_idx m' => true
  | Right_idx n', Right_idx m' => index_lt n' m'
  | Left_idx n', Left_idx m' => index_lt n' m'
  | _, _ => false
  end.

Lemma index_eq_prop : forall n m:index, index_eq n m = true -> n = m.
  simple induction n; simple induction m; simpl; intros.
  rewrite (H i0 H1); reflexivity.
  discriminate.
  discriminate.
  discriminate.
  rewrite (H i0 H1); reflexivity.
  discriminate.
  discriminate.
  discriminate.
  reflexivity.
Qed.

End variables_map.

Unset Implicit Arguments.
