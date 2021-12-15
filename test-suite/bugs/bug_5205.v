Definition foo (n : nat) (m : nat) : nat := m.

Arguments foo {_} _, _ _.

Check foo 1 1.
Check foo (n:=1) 1.
