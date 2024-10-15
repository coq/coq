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

Require Import ssrbool TestSuite.ssr_mini_mathcomp.

Parameter T : Type.

Lemma test0 : forall a b c d : T, True.
Proof. by move=> a b {a} a c; exact I. Qed.

Parameter P : T -> Prop.

Lemma test1 : forall a b c : T, P a -> forall d : T, True.
Proof. move=> a b {a} a _ d; exact I. Qed.

Definition Q := forall x y : nat, x = y.
Axiom L : 0 = 0 -> Q.
Axiom L' : 0 = 0 -> forall x y : nat, x = y.
Lemma test3 : Q.
by apply/L.
Undo.
rewrite /Q.
by apply/L.
Undo 2.
by apply/L'.
Qed.
