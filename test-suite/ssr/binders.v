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

Lemma test (x : bool) : True.
have H1 x := x.
have (x) := x => H2.
have H3 T (x : T) := x.
have ? : bool := H1 _ x.
have ? : bool := H2 _ x.
have ? : bool := H3 _ x.
have ? (z : bool) : forall y : bool, z = z := fun y => refl_equal _.
have ? w : w = w := @refl_equal nat w.
have ? y : true by [].
have ? (z : bool) : z = z.
  exact: (@refl_equal _ z).
have ? (z w : bool) : z = z by exact: (@refl_equal _ z).
have H w (a := 3) (_ := 4) : w && true = w.
  by rewrite andbT.
exact I.
Qed.

Lemma test1 : True.
suff (x : bool): x = x /\ True.
  by move/(_ true); case=> _.
split; first by exact: (@refl_equal _ x).
suff H y : y && true = y /\ True.
  by case: (H true).
suff H1 /= : true && true /\ True.
  by rewrite andbT; split; [exact: (@refl_equal _ y) | exact: I].
match goal with |- is_true true /\ True => idtac end.
by split.
Qed.

Lemma foo n : n >= 0.
have f i (j := i + n) : j < n.
  match goal with j := i + n |- _ => idtac end.
Undo 2.
suff f i (j := i + n) : j < n.
  done.
match goal with j := i + n |- _ => idtac end.
Undo 3.
done.
Qed.
