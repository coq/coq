(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
Require Import List.

Parameter in_list : list (nat * nat) -> nat -> Prop.
Definition not_in_list (l : list (nat * nat)) (n : nat) : Prop :=
  ~ in_list l n.

(* Hints Unfold not_in_list. *)

Axiom
  lem1 :
    forall (l1 l2 : list (nat * nat)) (n : nat),
    not_in_list (l1 ++ l2) n -> not_in_list l1 n.

Axiom
  lem2 :
    forall (l1 l2 : list (nat * nat)) (n : nat),
    not_in_list (l1 ++ l2) n -> not_in_list l2 n.

Axiom
  lem3 :
    forall (l : list (nat * nat)) (n p q : nat),
    not_in_list ((p, q) :: l) n -> not_in_list l n.

Axiom
  lem4 :
    forall (l1 l2 : list (nat * nat)) (n : nat),
    not_in_list l1 n -> not_in_list l2 n -> not_in_list (l1 ++ l2) n.

Hint Resolve lem1 lem2 lem3 lem4: essai.

Goal
forall (l : list (nat * nat)) (n p q : nat),
not_in_list ((p, q) :: l) n -> not_in_list l n.
intros.
 eauto with essai.
Qed.

(* Example from Nicolas Magaud on coq-club - Jul 2000 *)

Definition Nat : Set := nat.
Parameter S' : Nat -> Nat.
Parameter plus' : Nat -> Nat -> Nat.

Lemma simpl_plus_l_rr1 :
 (forall n0 : Nat,
  (forall m p : Nat, plus' n0 m = plus' n0 p -> m = p) ->
  forall m p : Nat, S' (plus' n0 m) = S' (plus' n0 p) -> m = p) ->
 forall n : Nat,
 (forall m p : Nat, plus' n m = plus' n p -> m = p) ->
 forall m p : Nat, S' (plus' n m) = S' (plus' n p) -> m = p.
intros.
 eauto. (* does EApply H *)
Qed.
