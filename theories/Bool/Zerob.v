(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Arith.
Require Import Bool.

Local Open Scope nat_scope.

Definition zerob (n:nat) : bool :=
  match n with
    | O => true
    | S _ => false
  end.

Lemma zerob_true_intro : forall n:nat, n = 0 -> zerob n = true.
Proof.
  destruct n; [ trivial with bool | inversion 1 ].
Qed.
Hint Resolve zerob_true_intro: bool.

Lemma zerob_true_elim : forall n:nat, zerob n = true -> n = 0.
Proof.
  destruct n; [ trivial with bool | inversion 1 ].
Qed.

Lemma zerob_false_intro : forall n:nat, n <> 0 -> zerob n = false.
Proof.
  destruct n; [ destruct 1; auto with bool | trivial with bool ].
Qed.
Hint Resolve zerob_false_intro: bool.

Lemma zerob_false_elim : forall n:nat, zerob n = false -> n <> 0.
Proof.
  destruct n; [ inversion 1 | auto with bool ].
Qed.
