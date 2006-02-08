(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Arith.
Require Import Compare_dec.
Require Import Wf_nat.

Declare ML Module "recdef".

Section Iter.
Variable A : Type.

Fixpoint iter (n : nat) : (A -> A) -> A -> A :=
  fun (fl : A -> A) (def : A) =>
  match n with
  | O => def
  | S m => fl (iter m fl def)
  end.
End Iter.

Theorem SSplus_lt : forall p p' : nat, p < S (S (p + p')).
auto with arith.
Qed.
 
Theorem Splus_lt : forall p p' : nat, p' < S (p + p').
auto with arith.
Qed.

Theorem le_lt_SS : forall x y, x <= y -> x < S (S y).
auto with arith.
Qed.

Inductive max_type (m n:nat) : Set :=
  cmt : forall v, m <= v -> n <= v -> max_type m n.

Definition max : forall m n:nat, max_type m n.
intros m n; case (le_gt_dec m n).
intros h; exists n; [exact h | apply le_n].
intros h; exists m; [apply le_n | apply lt_le_weak; exact h].
Defined.
