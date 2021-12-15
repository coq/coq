Fixpoint bug_1 (e1 : nat) {struct e1}
  : nat
with bug_2 {H_imp : nat} (e2 : nat) {struct e2}
  : nat.
Proof.
  - exact e1.
  - exact e2.
Admitted.

Fixpoint hbug_1 (a:bool) (e1 : nat) {struct e1}
  : nat
with hbug_2 (a:nat) (e2 : nat) {struct e2}
  : nat.
Proof.
  - exact e1.
  - exact e2.
Admitted.

Check (hbug_1 : bool -> nat -> nat).
Check (hbug_2 : nat -> nat -> nat).
