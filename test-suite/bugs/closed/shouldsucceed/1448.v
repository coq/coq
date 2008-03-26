Require Import Relations.
Require Import Setoid.
Require Import Ring_theory.
Require Import Ring_base.


Variable R : Type.
Variable Rone Rzero : R.
Variable Rplus Rmult Rminus : R -> R -> R.
Variable Rneg : R -> R.

Lemma my_ring_theory : @ring_theory R Rzero Rone Rplus Rmult Rminus Rneg (@eq
R).
Admitted.

Variable Req : R -> R -> Prop.

Hypothesis Req_refl : reflexive _ Req.
Hypothesis Req_sym : symmetric _ Req.
Hypothesis Req_trans : transitive _ Req.

Add Relation R Req
  reflexivity proved by Req_refl
  symmetry proved by Req_sym
  transitivity proved by Req_trans
  as Req_rel.

Add Ring my_ring : my_ring_theory (abstract).
