(* Check BZ#1025 submitted by Pierre-Luc Carmel Biron *)

Module Type FOO.
  Parameter A : Type.
End FOO.

Module Type BAR.
  Declare Module Foo : FOO.
End BAR.

Module Bar : BAR.

  Module Fu : FOO.
    Definition A := Prop.
  End Fu.

  Module Foo := Fu.

End Bar.

(* Check BZ#2809: correct printing of modules with notations *)

Module C.
  Inductive test : Type :=
    | c1 : test
    | c2 : nat -> test.

  Notation "! x" := (c2 x) (at level 50).
End C.

Print C. (* Should print test_rect without failing *)
