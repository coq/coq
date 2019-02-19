

Module Import M.
  Private Inductive Foo := .

  Definition nat_of_foo (f:Foo) : nat := match f with end.

  Scheme Induction for Foo Sort Set.
End M.

Fail Definition bool_of_foo (f:Foo) : bool := match f with end.

Fail Scheme Induction for Foo Sort Prop.

Module Import N.
  Private Inductive foo := C : foo -> foo.
End N.

(* For some reason this scheme didn't get caught even though the other
   one did. *)
Fail Scheme Induction for N.foo Sort Prop.
