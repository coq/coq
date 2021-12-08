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

Definition bar (t:=_) (x := true : t) := Eval native_compute in x.
Definition barvm (t:=_) (x := true : t) := Eval vm_compute in x.

Definition baz (z:nat) (t:=_ z) (x := true : t) := Eval native_compute in x.
Definition bazvm (z:nat) (t:=_ z) (x := true : t) := Eval vm_compute in x.
