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
Require Import ssrfun ssrbool TestSuite.ssr_mini_mathcomp.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma test0 (a b : unit) f : a = f b.
Proof. by rewrite !unitE.  Qed.

Lemma phE T : all_equal_to (Phant T). Proof. by case. Qed.

Lemma test1 (a b : phant nat) f : a = f b.
Proof.  by rewrite !phE.  Qed.

Lemma eq_phE (T : eqType) : all_equal_to (Phant T). Proof. by case. Qed.

Lemma test2 (a b : phant bool) f : a = locked (f b).
Proof. by rewrite !eq_phE. Qed.
