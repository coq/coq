Module Example1.

Module Type foo. Parameter A : Prop. End foo.
Module Type bar. Parameter B : Prop. End bar.

Module foobar <: foo <: bar.
Fail End foobar.
Include foo <+ bar.
End foobar.

Fail Module barfoo <: foo <: bar := foo.
Fail Module barfoo <: foo <: bar := bar.
Module barfoo <: foo <: bar := bar <+ foo.

Module foo' : foo := foo.

End Example1.

Module Example2.

Module Import bar.
Module foo.
End foo.
End bar.

Module empty.
End empty.

Fail Fail Module foo := foo.
Fail Fail Module foo := empty <+ foo.
Fail Fail Module foo := foo <+ empty.
(* This is in fact implemented as the following: *)
Module foo.
Include foo.
End foo.

End Example2.

Module Example3.

(* Check that an interactive module can refer to elements
   already defined in it *)
Module foo'.
Definition a := 0.
Definition b := foo'.a.
End foo'.

End Example3.
