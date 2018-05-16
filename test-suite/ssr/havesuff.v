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


Variables P G : Prop.

Lemma test1 : (P -> G) -> P -> G.
Proof.
move=> pg p.
have suff {pg} H : P.
  match goal with |- P -> G => move=> _; exact: pg p | _ => fail end.
match goal with H : P -> G |- G => exact: H p | _ => fail end.
Qed.

Lemma test2 : (P -> G) -> P -> G.
Proof.
move=> pg p.
have suffices {pg} H : P.
  match goal with |- P -> G => move=> _; exact: pg p | _ => fail end.
match goal with H : P -> G |- G => exact: H p | _ => fail end.
Qed.

Lemma test3 : (P -> G) -> P -> G.
Proof.
move=> pg p.
suff have {pg} H : P.
  match goal with H : P |- G => exact: pg H | _ => fail end.
match goal with |- (P -> G) -> G => move=> H; exact: H p | _ => fail end.
Qed.

Lemma test4 : (P -> G) -> P -> G.
Proof.
move=> pg p.
suffices have {pg} H: P.
  match goal with H : P |- G => exact: pg H | _ => fail end.
match goal with |- (P -> G) -> G => move=> H; exact: H p | _ => fail end.
Qed.

(*
Lemma test5 : (P -> G) -> P -> G.
Proof.
move=> pg p.
suff have {pg} H : P := pg H.
match goal with |- (P -> G) -> G => move=> H; exact: H p | _ => fail end.
Qed.
*)

(*
Lemma test6 : (P -> G) -> P -> G.
Proof.
move=> pg p.
suff have {pg} H := pg H.
match goal with |- (P -> G) -> G => move=> H; exact: H p | _ => fail end.
Qed.
*)

Lemma test7 : (P -> G) -> P -> G.
Proof.
move=> pg p.
have suff {pg} H : P := pg.
match goal with H : P -> G |- G => exact: H p | _ => fail end.
Qed.

Lemma test8 : (P -> G) -> P -> G.
Proof.
move=> pg p.
have suff {pg} H := pg.
match goal with H : P -> G |- G => exact: H p | _ => fail end.
Qed.

Goal forall x y : bool, x = y -> x = y.
move=> x y E.
by have {x E} -> : x = y by [].
Qed.
