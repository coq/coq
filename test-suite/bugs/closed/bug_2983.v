Module Type ModA.
End ModA.
Module Type ModB(A : ModA).
End ModB.
Module Foo(A : ModA)(B : ModB A).
End Foo.

Print Module Foo.
