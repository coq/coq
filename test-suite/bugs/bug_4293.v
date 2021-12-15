Module Type Foo.
Definition T := let X := Type in Type.
End Foo.

Module M : Foo.
Definition T := let X := Type in Type.
End M.
