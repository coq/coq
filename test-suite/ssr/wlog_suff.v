(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)

Require Import ssreflect.
Require Import ssrbool.

Lemma test b : b || ~~b.
wlog _ : b / b = true.
  case: b; [ by apply | by rewrite orbC ].
wlog suff: b /  b || ~~b.
  by case: b.
by case: b.
Qed.

Lemma test2 b c (H : c = b) : b || ~~b.
wlog _ : b {c H} / b = true.
  by case: b H.
by case: b.
Qed.
