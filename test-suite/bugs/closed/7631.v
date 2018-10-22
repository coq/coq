Module NamedContext.

Definition foo := true.

Section Foo.

Let bar := foo.

Eval native_compute in bar.
Eval vm_compute in bar.

End Foo.

End NamedContext.

Module RelContext.

Definition foo := true.

Definition bar (x := foo) := Eval native_compute in x.
Definition barvm (x := foo) := Eval vm_compute in x.

End RelContext.
