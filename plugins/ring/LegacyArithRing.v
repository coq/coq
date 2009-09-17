(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* Instantiation of the Ring tactic for the naturals of Arith $*)

Require Import Bool.
Require Export LegacyRing.
Require Export Arith.
Require Import Eqdep_dec.

Open Local Scope nat_scope.

Unboxed Fixpoint nateq (n m:nat) {struct m} : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => nateq n' m'
  | _, _ => false
  end.

Lemma nateq_prop : forall n m:nat, Is_true (nateq n m) -> n = m.
Proof.
  simple induction n; simple induction m; intros; try contradiction.
  trivial.
  unfold Is_true in H1.
  rewrite (H n1 H1).
  trivial.
Qed.

Hint Resolve nateq_prop: arithring.

Definition NatTheory : Semi_Ring_Theory plus mult 1 0 nateq.
  split; intros; auto with arith arithring.
(*  apply (fun n m p:nat => plus_reg_l m p n) with (n := n).
  trivial.*)
Defined.


Add Legacy Semi Ring nat plus mult 1 0 nateq NatTheory [ 0 S ].

Goal forall n:nat, S n = 1 + n.
intro; reflexivity.
Save S_to_plus_one.

(* Replace all occurrences of (S exp) by (plus (S O) exp), except when
   exp is already O and only for those occurrences than can be reached by going
   down plus and mult operations  *)
Ltac rewrite_S_to_plus_term t :=
  match constr:t with
  | 1 => constr:1
  | (S ?X1) =>
      let t1 := rewrite_S_to_plus_term X1 in
      constr:(1 + t1)
  | (?X1 + ?X2) =>
      let t1 := rewrite_S_to_plus_term X1
      with t2 := rewrite_S_to_plus_term X2 in
      constr:(t1 + t2)
  | (?X1 * ?X2) =>
      let t1 := rewrite_S_to_plus_term X1
      with t2 := rewrite_S_to_plus_term X2 in
      constr:(t1 * t2)
  | _ => constr:t
  end.

(* Apply S_to_plus on both sides of an equality *)
Ltac rewrite_S_to_plus :=
  match goal with
  |  |- (?X1 = ?X2) =>
      try
       let t1 :=
       (**)  (**)
       rewrite_S_to_plus_term X1
       with t2 := rewrite_S_to_plus_term X2 in
       change (t1 = t2) in |- *
  |  |- (?X1 = ?X2) =>
      try
       let t1 :=
       (**)  (**)
       rewrite_S_to_plus_term X1
       with t2 := rewrite_S_to_plus_term X2 in
       change (t1 = t2) in |- *
  end.

Ltac ring_nat := rewrite_S_to_plus; ring.
