Inductive foo := Foo (x:nat) (H: x=x).
Inductive foo2 := Foo2 (x : nat).
Inductive foo3 := Foo3 (f : foo2).

Goal foo.
  Fail apply Foo.
  Fail apply Foo2.
  Fail apply Foo3.
Abort.
