(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Ltac ccsolve :=
  repeat
   match goal with
   | H:?X1 |- ?X2 =>
       let Heq := fresh "Heq" in
       (assert (Heq : X2 = X1); [ congruence | rewrite Heq; exact H ])
   | H:?X1,G:(?X2 -> ?X3) |- _ =>
       let Heq := fresh "Heq" in
       (assert (Heq : X2 = X1);
         [ congruence
         | rewrite Heq in G; generalize (G H); clear G; intro G ])
   end.  
