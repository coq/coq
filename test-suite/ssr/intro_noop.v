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
Axiom daemon : False. Ltac myadmit := case: daemon.

Lemma v : True -> bool -> bool. Proof. by []. Qed.

Reserved Notation " a -/ b " (at level 0).
Reserved Notation " a -// b " (at level 0).
Reserved Notation " a -/= b " (at level 0).
Reserved Notation " a -//= b " (at level 0).

Lemma test : forall a b c, a || b || c.
Proof.
move=> ---a--- - -/=- -//- -/=- -//=- b [|-].
move: {-}a => /v/v-H; have _ := H I I.
Fail move: {-}a {H} => /v-/v-H.
have - -> : a = (id a) by [].
have --> : a = (id a) by [].
have - - _ : a = (id a) by [].
have -{1}-> : a = (id a) by [].
  by myadmit.
move: a.
case: b => -[] //.
by myadmit.
Qed.
