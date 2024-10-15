(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(**** Tactics Tauto and Intuition ****)

(**** Tauto:
  Tactic for automating proof in Intuionnistic Propositional Calculus, based on
  the contraction-free LJT of Dickhoff ****)

(**** Intuition:
  Simplifications of goals, based on LJT calcul ****)

(* Fails because Tauto does not perform any Apply *)
Goal (forall A : Prop, A \/ ~ A) -> forall x y : nat, x = y \/ x <> y.
Proof.
   Fail tauto.
Abort.
