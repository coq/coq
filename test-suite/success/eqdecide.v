(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Inductive T : Set :=
  | A : T
  | B : T -> T.

Lemma lem1 : forall x y : T, {x = y} + {x <> y}.
 decide equality.
Qed.

Lemma lem1' : forall x y : T, x = y \/ x <> y.
 decide equality.
Qed.

Lemma lem1'' : forall x y : T, {x <> y} + {x = y}.
 decide equality.
Qed.

Lemma lem1''' : forall x y : T, x <> y \/ x = y.
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

