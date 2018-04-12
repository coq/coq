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

Lemma test1 : forall a b : nat, a == b -> a == 0 -> b == 0.
Proof. move=> a b Eab Eac; congr (_ == 0) : Eac; exact: eqP Eab. Qed.

Definition arrow A B := A -> B.

Lemma test2 : forall a b : nat, a == b -> arrow (a == 0) (b == 0).
Proof. move=> a b Eab; congr (_ == 0); exact: eqP Eab. Qed.

Definition equals T (A B : T) := A = B.

Lemma test3 : forall a b : nat, a = b -> equals nat (a + b) (b + b).
Proof. move=> a b E; congr (_ + _); exact E. Qed.

Variable S : eqType.
Variable f : nat -> S.
Coercion f : nat >-> Equality.sort.

Lemma test4 : forall a b : nat, b = a -> @eq S (b + b) (a + a).
Proof. move=> a b Eba; congr (_ + _); exact:  Eba. Qed.
