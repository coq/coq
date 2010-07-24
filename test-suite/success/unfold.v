(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(* Test le Hint Unfold sur des var locales *)

Section toto.
Let EQ := @eq.
Goal EQ nat 0 0.
Hint Unfold EQ.
auto.
Qed.
