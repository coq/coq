Module Example1.
Notation zero := (ltac: (exact 0)).

Definition f (m n : nat) : nat := m.
Notation fzero m := (f zero m).

Lemma test : False.
eset (H := fzero _).
Abort.
End Example1.

Module Example2.
Definition f (m n : nat) : nat := m.
Notation f_exact_zero m := (f (ltac: (exact 0)) m).

Lemma test : False.
eset (H := f_exact_zero _).
Abort.
End Example2.

Module ReducedExample.
Notation foo x := (ltac:(exact tt)).
Check foo _.
End ReducedExample.
