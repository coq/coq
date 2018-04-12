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

Axiom daemon : False. Ltac myadmit := case: daemon.

Class foo (T : Type) := { n : nat }.
Instance five : foo nat := {| n := 5 |}.

Definition bar T {f : foo T} m : Prop :=
  @n _ f = m.

Eval compute in (bar nat 7).

Lemma a : True.
set toto := bar _ 8.
have titi : bar _ 5.
  reflexivity.
have titi2 : bar _ 5 := .
  Fail reflexivity.
  by myadmit.
have totoc (H : bar _ 5) : 3 = 3 := eq_refl.
move/totoc: nat => _.
exact I.
Qed.

Set SsrHave NoTCResolution.

Lemma a' : True.
set toto := bar _ 8.
have titi : bar _ 5.
  Fail reflexivity.
  by myadmit.
have titi2 : bar _ 5 := .
  Fail reflexivity.
  by myadmit.
have totoc (H : bar _ 5) : 3 = 3 := eq_refl.
move/totoc: nat => _.
exact I.
Qed.
