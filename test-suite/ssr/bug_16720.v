From Stdlib Require Import ssreflect.
Class Trivial := trivial {}.
#[local] Existing Instance trivial.
Goal Trivial.
  Succeed assert True.
  have: True.
    match goal with |- True => admit end.
  match goal with |- True -> Trivial => admit end.
Abort.

From Stdlib Require Import DecidableClass.

Goal True.
Proof.
  (* Works as expected. *)
  have P_iff : (forall n, n = 0 <-> 0 = n).
    match goal with |-  (forall n, n = 0 <-> 0 = n) => admit end.
  match goal with P_iff : (forall n, n = 0 <-> 0 = n) |- True => admit end.
Abort.

From Stdlib Require Import Bool.

Goal forall (x y : bool), Decidable (eq x y).
Proof.
  Succeed apply _.
  have P_iff : (forall n, n = 0 <-> 0 = n).
    match goal with |-  (forall n, n = 0 <-> 0 = n) => admit end.
  match goal with P_iff : (forall n, n = 0 <-> 0 = n) |- forall (x y : bool), Decidable (eq x y) => admit end.
Abort.
