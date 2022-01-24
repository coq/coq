(* Sections taking care of let-ins for inductive types *)

Section Foo.

Fail Inductive foo (A : Type) (x : A) (y := x) (y : A) := Foo.
Inductive foo (A : Type) (x : A) (y := x) (y' : A) := Foo.

End Foo.

Section Foo2.

Variable B : Type.
Variable b : B.
Let c := b.
Fail Inductive foo2 (A : Type) (x : A) (y := x) (y : A) := Foo2 : c=c -> foo2 A x y.
Inductive foo2 (A : Type) (x : A) (y' := x) (y : A) := Foo2 : c=c -> foo2 A x y.

End Foo2.
