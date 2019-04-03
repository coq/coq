Require Import Lia.
Require Import Omega.
Set Primitive Projections.

Record foo (a: unit) := { field: nat }.

Notation goal := (forall x, field tt x = 1 -> field tt x = 1).

Lemma test_omega : goal.
Proof. intros. cbv [field]. omega. Qed.

Lemma test_lia : goal.
Proof. intros. cbv [field]. lia. Qed.
