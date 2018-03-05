(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(* Test le Hint Unfold sur des var locales *)

Section toto.
Let EQ := @eq.
Goal EQ nat 0 0.
Hint Unfold EQ.
auto.
Qed.

(* Check regular failure when statically existing ref does not exist
   any longer at run time *)

Goal let x := 0 in True.
intro x.
Fail (clear x; unfold x).
Abort.
