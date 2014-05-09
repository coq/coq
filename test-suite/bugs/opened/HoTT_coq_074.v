Monomorphic Definition U1 := Type.
Monomorphic Definition U2 := Type.

Set Printing Universes.
Definition foo : True.
Fail let t1 := type of U1 in
let t2 := type of U2 in
pose (t1 : t2). (* Error:
The term "Type (* Top.1+1 *)" has type "Type (* Top.1+2 *)"
while it is expected to have type "Type (* Top.2+1 *)". *)
exact I.
Defined.
