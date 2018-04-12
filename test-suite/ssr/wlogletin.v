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
Require Import ssrbool.
Require Import TestSuite.ssr_mini_mathcomp.

Variable T : Type.
Variables P : T -> Prop.

Definition f := fun x y : T => x.

Lemma test1 : forall x y : T, P (f x y) -> P x.
Proof.
move=> x y; set fxy := f x y; move=> Pfxy.
wlog H : @fxy Pfxy / P x.
  match goal with |- (let fxy0 := f x y in P fxy0 -> P x -> P x) -> P x => by auto | _ => fail end.
exact: H.
Qed.

Lemma test2 : forall x y : T, P (f x y) -> P x.
Proof.
move=> x y; set fxy := f x y; move=> Pfxy.
wlog H : fxy Pfxy / P x.
  match goal with |- (forall fxy, P fxy -> P x -> P x) -> P x => by auto | _ => fail end.
exact: H.
Qed.

Lemma test3 : forall x y : T, P (f x y) -> P x.
Proof.
move=> x y; set fxy := f x y; move=> Pfxy.
move: {1}@fxy (Pfxy) (Pfxy).
match goal with |- (let fxy0 := f x y in P fxy0 -> P fxy -> P x) => by auto | _ => fail end.
Qed.

Lemma test4 : forall n m z: bool, n = z -> let x := n in x = m && n -> x = m && n.
move=> n m z E x H.
case: true.
  by rewrite {1 2}E in (x) H |- *.
by rewrite {1}E in x H |- *.
Qed.
