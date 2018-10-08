(* Sections taking care of let-ins for inductive types *)

Section Foo.

Inductive foo (A : Type) (x : A) (y := x) (y : A) := Foo.

End Foo.

Section Foo2.

Variable B : Type.
Variable b : B.
Let c := b.
Inductive foo2 (A : Type) (x : A) (y := x) (y : A) := Foo2 : c=c -> foo2 A x y.

End Foo2.
