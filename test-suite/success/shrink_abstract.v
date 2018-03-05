Definition foo : forall (n m : nat), bool.
Proof.
pose (p := 0).
intros n.
pose (q := n).
intros m.
pose (r := m).
abstract (destruct m; [left|right]).
Defined.

Check (foo_subproof : nat -> bool).
