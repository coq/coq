Require Import Setoid.

Definition block A (a : A) := a.

Goal forall A (a : A), block Type nat.
Proof.
Fail reflexivity.

