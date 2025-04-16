Class Foo := foo : nat.

Definition foo_0 : Foo := 0.

Module X.
  Global Existing Instance foo_0 | 1.
End X.

Existing Instance foo_0 | 2.

Import X.

Print Instances Foo.
