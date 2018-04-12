(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)

Require Import ssreflect.
Require Import ssrbool TestSuite.ssr_mini_mathcomp.
(* div fintype finfun path bigop. *)

Axiom daemon : False. Ltac myadmit := case: daemon.

Lemma big_load R (K K' : R -> Type) idx op I r (P : pred I) F :
  let s := \big[op/idx]_(i <- r | P i) F i in
  K s * K' s -> K' s.
Proof. by move=> /= [_]. Qed.
Arguments big_load [R] K [K' idx op I r P F].

Section Elim1.

Variables (R : Type) (K : R -> Type) (f : R -> R).
Variables (idx : R) (op op' : R -> R -> R).

Hypothesis Kid : K idx.

Ltac ASSERT1 := match goal with |- (K idx) => myadmit end.
Ltac ASSERT2 K := match goal with |- (forall x1 : R, R ->
    forall y1 : R, R -> K x1 -> K y1 -> K (op x1 y1)) => myadmit end.


Lemma big_rec I r (P : pred I) F
    (Kop : forall i x, P i -> K x -> K (op (F i) x)) :
  K (\big[op/idx]_(i <- r | P i) F i).
Proof.
elim/big_ind2: {-}_.
  ASSERT1. ASSERT2 K. match goal with |- (forall i : I, is_true (P i) -> K (F i)) => myadmit end. Undo 4.
elim/big_ind2: _ / {-}_.
  ASSERT1. ASSERT2 K. match goal with |- (forall i : I, is_true (P i) -> K (F i)) => myadmit end. Undo 4.

elim/big_rec2: (\big[op/idx]_(i <- r | P i) op idx (F i))
  / (\big[op/idx]_(i <- r | P i) F i).
  ASSERT1. match goal with |- (forall i : I, R -> forall y2 : R, is_true (P i) -> K y2 -> K (op (F i) y2)) => myadmit end. Undo 3.

elim/(big_load (phantom R)): _.
  Undo.

Fail elim/big_rec2: {2}_.

elim/big_rec2: (\big[op/idx]_(i <- r | P i) F i)
  / {1}(\big[op/idx]_(i <- r | P i) F i).
  Undo.

elim/(big_load (phantom R)): _.
Undo.

Fail elim/big_rec2: _ / {2}(\big[op/idx]_(i <- r | P i) F i).
Admitted.

Definition morecomplexthannecessary A (P : A -> A -> Prop) x y := P x y.

Lemma grab A (P : A -> A -> Prop) n m : (n = m) -> (P n n) -> morecomplexthannecessary A P n m.
by move->.
Qed.

Goal forall n m, m + (n + m) = m + (n * 1 + m).
Proof. move=> n m; elim/grab : (_ * _) / {1}n => //; exact: muln1. Qed.

End Elim1.
