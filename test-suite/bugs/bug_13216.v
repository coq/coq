Class A.
Declare Instance a:A.
Inductive T `(A) := C.
Definition f x := match x with C _ => 0 end.
