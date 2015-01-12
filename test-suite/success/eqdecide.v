(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Inductive T : Set :=
  | A : T
  | B : T -> T.

Lemma lem1 : forall x y : T, {x = y} + {x <> y}.
 decide equality.
Qed.

Lemma lem2 : forall x y : T, {x = y} + {x <> y}.
intros x y.
 decide equality.
Qed.

Lemma lem4 : forall x y : T, {x = y} + {x <> y}.
intros x y.
 compare x y; auto.
Qed.

