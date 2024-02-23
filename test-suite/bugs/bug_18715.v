Section Foo.

Variable f : nat -> nat.

Definition foo := f 0.

Eval native_compute in foo.

End Foo.

Set Universe Polymorphism.

Section Bar.

Universe u.

Variable f : nat -> Type@{u}.
Definition bar := f 0.

Eval native_compute in bar.

End Bar.
