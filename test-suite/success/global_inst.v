
Class Foo := foo : nat.

Module X.
  Module Y.
    Global Instance n_0 : Foo := 0.
  End Y.
End X.

Definition inferred_0 : nat := foo.

Check eq_refl : inferred_0 = 0.

Instance n_1 : Foo := 1.

Definition inferred_1 : nat := foo.

Check eq_refl : inferred_1 = 1.

Import X.

Definition inferred_1' : nat := foo.

Check eq_refl : inferred_1' = 1.

Import Y.

Definition inferred_1'' : nat := foo.

Check eq_refl : inferred_1'' = 1.
