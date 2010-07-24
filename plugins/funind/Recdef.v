(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
Require Compare_dec.
Require Wf_nat.

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
  intro p; intro p'; change (S p <= S (S (p + p')));
    apply le_S; apply Gt.gt_le_S; change (p < S (p + p'));
    apply Lt.le_lt_n_Sm; apply Plus.le_plus_l.
Qed.


Theorem Splus_lt : forall p p' : nat, p' < S (p + p').
  intro p; intro p'; change (S p' <= S (p + p'));
    apply Gt.gt_le_S; change (p' < S (p + p')); apply Lt.le_lt_n_Sm;
       apply Plus.le_plus_r.
Qed.

Theorem le_lt_SS : forall x y, x <= y -> x < S (S y).
intro x; intro y; intro H; change (S x <= S (S y));
    apply le_S; apply Gt.gt_le_S; change (x < S y);
    apply Lt.le_lt_n_Sm; exact H.
Qed.

Inductive max_type (m n:nat) : Set :=
  cmt : forall v, m <= v -> n <= v -> max_type m n.

Definition max : forall m n:nat, max_type m n.
intros m n; case (Compare_dec.le_gt_dec m n).
intros h; exists n; [exact h | apply le_n].
intros h; exists m; [apply le_n | apply Lt.lt_le_weak; exact h].
Defined.
