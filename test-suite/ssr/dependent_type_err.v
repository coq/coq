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
Require Import ssrfun ssrbool TestSuite.ssr_mini_mathcomp.

Lemma ltn_leq_trans : forall n m p : nat, m < n -> n <= p -> m < p.
move=> n m p Hmn Hnp; rewrite -ltnS.
Fail rewrite (_ : forall n0 m0 p0 : nat, m0 <= n0 -> n0 < p0 -> m0 < p0).
Fail rewrite leq_ltn_trans.
Admitted.
