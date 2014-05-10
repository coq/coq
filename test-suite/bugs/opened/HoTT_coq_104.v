Set Implicit Arguments.

Require Import Logic.

Global Set Universe Polymorphism.
Global Set Asymmetric Patterns.
Local Set Record Elimination Schemes.
Local Set Primitive Projections.

Record prod (A B : Type) : Type :=
  pair { fst : A; snd : B }.

Fail Check fun x : prod Set Set => eq_refl : x = pair (fst x) (snd x).
