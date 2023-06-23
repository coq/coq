Ltac wait n := match n with 0 => idtac | S ?n => wait n; wait n end.

#[deprecated(since="8.16")] Notation tt0 := tt.

Goal True.
Proof.
fail.
Qed.

Variable (n : nat).

Goal True.
Proof.
wait 18.
elim tt0.
Qed.
