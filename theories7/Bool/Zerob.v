(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Arith.
Require Bool.

V7only [Import nat_scope.].
Open Local Scope nat_scope.

Definition zerob : nat->bool 
      := [n:nat]Cases n of O => true | (S _) => false end.

Lemma zerob_true_intro : (n:nat)(n=O)->(zerob n)=true.
NewDestruct n; [Trivial with bool | Inversion 1].
Qed.
Hints Resolve zerob_true_intro : bool.

Lemma zerob_true_elim : (n:nat)(zerob n)=true->(n=O).
NewDestruct n; [Trivial with bool | Inversion 1].
Qed.

Lemma zerob_false_intro : (n:nat)~(n=O)->(zerob n)=false.
NewDestruct n; [NewDestruct 1; Auto with bool | Trivial with bool].
Qed.
Hints Resolve zerob_false_intro : bool.

Lemma zerob_false_elim : (n:nat)(zerob n)=false -> ~(n=O).
NewDestruct n; [Intro H; Inversion H | Auto with bool].
Qed.
