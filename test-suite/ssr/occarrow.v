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
Require Import TestSuite.ssr_mini_mathcomp.

Lemma test1 : forall n m : nat, n = m -> m * m + n * n = n * n + n * n.
move=> n m E; have [{2}-> _] : n * n = m * n /\ True by move: E => {1}<-.
by move: E => {3}->.
Qed.

Lemma test2 : forall n m : nat, True /\ (n = m -> n * n = n * m).
by move=> n m; constructor=> [|{2}->].
Qed.
