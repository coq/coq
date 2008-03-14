(* Check bug #1025 submitted by Pierre-Luc Carmel Biron *)

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
