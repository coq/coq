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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* error 1 *)

Ltac subst1 H := move: H; rewrite {1} addnC; move => H.
Ltac subst2 H := rewrite addnC in H.

Goal ( forall a b: nat, b+a = 0 -> b+a=0).
Proof. move=> a b hyp. subst1 hyp. subst2 hyp. done. Qed.
