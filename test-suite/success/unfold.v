(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(* Test le Hint Unfold sur des var locales *)

Section toto.
Local EQ:=eq.
Goal (EQ nat O O).
Hints Unfold EQ.
Auto.
Save.
