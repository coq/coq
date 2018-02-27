(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(**** Tests of Field with real numbers ****)

Require Import Reals RealField.
Open Scope R_scope.

(* Example 1 *)
Goal
forall eps : R,
eps * (1 / (2 + 2)) + eps * (1 / (2 + 2)) = eps * (1 / 2).
Proof.
  intros.
   field.
Qed.

(* Example 2 *)
Goal
forall (f g : R -> R) (x0 x1 : R),
(f x1 - f x0) * (1 / (x1 - x0)) + (g x1 - g x0) * (1 / (x1 - x0)) =
(f x1 + g x1 - (f x0 + g x0)) * (1 / (x1 - x0)).
Proof.
  intros.
   field.
Abort.

(* Example 3 *)
Goal forall a b : R, 1 / (a * b) * (1 / (1 / b)) = 1 / a.
Proof.
  intros.
   field.
Abort.

Goal forall a b : R, 1 / (a * b) * (1 / 1 / b) = 1 / a.
Proof.
  intros.
   field_simplify_eq.
Abort.

Goal forall a b : R, 1 / (a * b) * (1 / 1 / b) = 1 / a.
Proof.
  intros.
   field_simplify (1 / (a * b) * (1 / 1 / b)).
Abort.

(* Example 4 *)
Goal
forall a b : R, a <> 0 -> b <> 0 -> 1 / (a * b) / (1 / b) = 1 / a.
Proof.
  intros.
   field; auto.
Qed.

(* Example 5 *)
Goal forall a : R, 1 = 1 * (1 / a) * a.
Proof.
  intros.
   field.
Abort.

(* Example 6 *)
Goal forall a b : R, b = b * / a * a.
Proof.
  intros.
   field.
Abort.

(* Example 7 *)
Goal forall a b : R, b = b * (1 / a) * a.
Proof.
  intros.
   field.
Abort.

(* Example 8 *)
Goal forall x y : R,
  x * (1 / x + x / (x + y)) =
  - (1 / y) * y * (- (x * (x / (x + y))) - 1).
Proof.
  intros.
   field.
Abort.

(* Example 9 *)
Goal forall a b : R, 1 / (a * b) * (1 / 1 / b) = 1 / a -> False.
Proof.
intros.
field_simplify_eq in H.
Abort.
