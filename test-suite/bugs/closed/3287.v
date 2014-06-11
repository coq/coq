Module Foo.
(* Definition foo := (I,I). *)
Definition bar := true.
End Foo.

Recursive Extraction Foo.bar.

Module Foo'.
Definition foo := (I,I).
Definition bar := true.
End Foo'.

Recursive Extraction Foo'.bar.

Module Foo''.
Definition foo := (I,I).
Definition bar := true.
End Foo''.

Extraction Foo.bar.
