(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(**** Tactics Tauto and Intuition ****)

(**** Tauto:
  Tactic for automating proof in Intuionnistic Propositional Calculus, based on
  the contraction-free LJT of Dickhoff ****)

(**** Intuition:
  Simplifications of goals, based on LJT calcul ****)

(* Fails because Tauto does not perform any Apply *)
Goal ((A:Prop)A\/~A)->(x,y:nat)(x=y\/~x=y).
Proof.
  Tauto.
