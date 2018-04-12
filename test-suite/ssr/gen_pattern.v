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

Notation "( a 'in' c )" := (a + c) (only parsing) : myscope.
Delimit Scope myscope with myscope.

Notation "( a 'in' c )" := (a + c) (only parsing).

Lemma foo x y : x + x.+1 = x.+1 + y.
move: {x} (x.+1) {1}x y (x.+1 in RHS).
  match goal with |- forall a b c d, b + a = d + c => idtac end.
Admitted.

Lemma bar x y : x + x.+1 = x.+1 + y.
move E: ((x.+1 in y)) => w.
  match goal with |- x + x.+1 = w => rewrite -{w}E end.
move E: (x.+1 in y)%myscope => w.
  match goal with |- x + x.+1 = w => rewrite -{w}E end.
move E: ((x + y).+1 as RHS) => w.
  match goal with |- x + x.+1 = w => rewrite -{}E -addSn end.
Admitted.
