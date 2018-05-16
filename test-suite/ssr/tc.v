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


Class foo (A : Type) : Type := mkFoo { val : A }.
Instance foo_pair {A B} {f1 : foo A} {f2 : foo B} : foo (A * B) | 2 :=
  {| val := (@val _ f1, @val _ f2) |}.
Instance foo_nat : foo nat | 3 := {| val := 0 |}.

Definition id {A} (x : A) := x.
Axiom E : forall A {f : foo A} (a : A), id a = (@val _ f).

Lemma test (x : nat) : id true = true -> id x = 0.
Proof.
Fail move=> _; reflexivity.
Timeout 2 rewrite E => _; reflexivity.
Qed.

Definition P {A} (x : A) : Prop := x = x.
Axiom V : forall A {f : foo A} (x:A), P x -> P (id x).

Lemma test1 (x : nat) : P x -> P (id x).
Proof.
move=> px.
Timeout 2 Fail move/V: px.
Timeout 2 move/V : (px) => _.
move/(V nat) : px => H; exact H.
Qed.
