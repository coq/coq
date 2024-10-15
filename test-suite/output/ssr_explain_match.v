(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ssrmatching.
Require Import ssreflect ssrbool TestSuite.ssr_mini_mathcomp.

Definition addnAC := (addnA, addnC).

Lemma test x y z : x + y + z =  x + y.

ssrinstancesoftpat (_ + _).
ssrinstancesofruleL2R addnC.
ssrinstancesofruleR2L addnA.
ssrinstancesofruleR2L addnAC.
Fail ssrinstancesoftpat (_ + _ in RHS). (* Not implemented *)
Admitted.
