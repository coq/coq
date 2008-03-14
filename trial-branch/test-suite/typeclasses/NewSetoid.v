(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certified Haskell Prelude.
 * Author: Matthieu Sozeau
 * Institution: LRI, CNRS UMR 8623 - Universit�copyright Paris Sud
 *              91405 Orsay, France *)

(* $Id: FSetAVL_prog.v 616 2007-08-08 12:28:10Z msozeau $ *)

Require Import Coq.Program.Program.

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Classes.SetoidTactics.

Goal not True == not (not False) -> ((not True -> True)) \/ True.
  intros.
  clrewrite H.
  clrewrite <- H.
  right ; auto.
Defined.

Definition reduced_thm := Eval compute in Unnamed_thm.

(* Print reduced_thm. *)

Lemma foo [ Setoid a R ] : True. (* forall x y, R x y -> x -> y. *)
Proof.
  intros.
  Print respect2.
  pose setoid_morphism.
  pose (respect2 (b0:=b)).
  simpl in b0.
  unfold binary_respectful in b0.
  pose (arrow_morphism R).
  pose (respect2 (b0:=b1)).
  unfold binary_respectful in b2.

  pose (eq_morphism (A:=a)).
  pose (respect2 (b0:=b3)).
  unfold binary_respectful in b4.
  exact I.
Qed.

Goal forall A B C (H : A <-> B) (H' : B <-> C), A /\ B <-> B /\ C.
  intros.
  Set Printing All.
  Print iff_morphism.
  clrewrite H.
  clrewrite H'.
  reflexivity.
Defined.

Goal forall A B C (H : A <-> B) (H' : B <-> C), A /\ B <-> B /\ C.
  intros.
  rewrite H.
  rewrite H'.
  reflexivity.
Defined.

Require Import Setoid_tac.
Require Import Setoid_Prop.

(* Print Unnamed_thm0. *)
(* Print Unnamed_thm1. *)


