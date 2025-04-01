Require Import Ltac2.Ltac2.

Ltac2 Notation "Assume" _(lconstr) := constructor.

Goal forall n : nat, True.
Proof.
  intros n.
  Assume n < 10.
Abort.

Ltac2 Notation "Assume_open" _(open_lconstr) := constructor.

Goal forall n : nat, True.
Proof.
  intros n.
  Assume_open n < 10.
Abort.
