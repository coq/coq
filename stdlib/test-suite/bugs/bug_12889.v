From Stdlib Require Import Relations.
From Stdlib Require Import Setoid.
From Stdlib Require Import Ring_theory.
From Stdlib Require Import Ring_base.

Section S1.
Variable R : Type.
Variable Rone Rzero : R.
Variable Rplus Rmult Rminus : R -> R -> R.
Variable Rneg : R -> R.

Lemma my_ring_theory1 : @ring_theory R Rzero Rone Rplus Rmult Rminus Rneg (@eq
R).
Admitted.
Add Ring my_ring : my_ring_theory1.
End S1.

Section S2.
Variable R : Type.
Variable Rone Rzero : R.
Variable Rplus Rmult Rminus : R -> R -> R.
Variable Rneg : R -> R.

Lemma my_ring_theory2 : @ring_theory R Rzero Rone Rplus Rmult Rminus Rneg (@eq
R).
Admitted.
Add Ring my_ring : my_ring_theory2.
End S2.
