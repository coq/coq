Require Import Program.

Class Foo (A : Type) := foo : A.

Unset Refine Instance Mode.
Program Instance f1 : Foo nat := S _.
