Module M.
Private Inductive foo := C : foo -> foo.
End M.

Fail Scheme Induction for M.foo Sort Prop.
