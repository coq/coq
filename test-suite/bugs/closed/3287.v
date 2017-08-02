Require Coq.extraction.Extraction.

Module Foo.
(* Definition foo := (I,I). *)
Definition bar := true.
End Foo.

Recursive Extraction Foo.bar.
Extraction TestCompile Foo.bar.

Module Foo'.
Definition foo := (I,I).
Definition bar := true.
End Foo'.

Recursive Extraction Foo'.bar.
Extraction TestCompile Foo'.bar.

Extraction Foo'.bar.
