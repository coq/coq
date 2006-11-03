(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: Field.v 7693 2005-12-21 23:50:17Z herbelin $ *)

(**** Tests of Field with real numbers ****)

Require Import Reals LegacyRfield.

(* Example 1 *)
Goal
forall eps : R,
(eps * (1 / (2 + 2)) + eps * (1 / (2 + 2)))%R = (eps * (1 / 2))%R.
Proof.
  intros.
   legacy field.
Abort.

(* Example 2 *)
Goal
forall (f g : R -> R) (x0 x1 : R),
((f x1 - f x0) * (1 / (x1 - x0)) + (g x1 - g x0) * (1 / (x1 - x0)))%R =
((f x1 + g x1 - (f x0 + g x0)) * (1 / (x1 - x0)))%R.
Proof.
  intros.
   legacy field.
Abort.
 
(* Example 3 *)
Goal forall a b : R, (1 / (a * b) * (1 / 1 / b))%R = (1 / a)%R.
Proof.
  intros.
   legacy field.
Abort.
 
(* Example 4 *)
Goal
forall a b : R, a <> 0%R -> b <> 0%R -> (1 / (a * b) / 1 / b)%R = (1 / a)%R.
Proof.
  intros.
   legacy field.
Abort.
 
(* Example 5 *)
Goal forall a : R, 1%R = (1 * (1 / a) * a)%R.
Proof.
  intros.
   legacy field.
Abort.
 
(* Example 6 *)
Goal forall a b : R, b = (b * / a * a)%R.
Proof.
  intros.
   legacy field.
Abort.
 
(* Example 7 *)
Goal forall a b : R, b = (b * (1 / a) * a)%R.
Proof.
  intros.
   legacy field.
Abort.

(* Example 8 *)
Goal
forall x y : R,
(x * (1 / x + x / (x + y)))%R =
(- (1 / y) * y * (- (x * (x / (x + y))) - 1))%R.
Proof.
  intros.
   legacy field.
Abort.
