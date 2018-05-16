(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ssreflect.

Set Implicit Arguments.

Axiom P : nat -> nat -> Prop.

Axiom tr :
  forall x y z, P x y -> P y z -> P x z.

Lemma test a b c : P a c -> P a b.
Proof.
intro H.
Fail have [: s1 s2] H1 : P a b := @tr _ _ _ s1 s2.
have [: w s1 s2] H1 : P a b := @tr _ w _ s1 s2.
Abort.
