(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Ltac CCsolve :=
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
