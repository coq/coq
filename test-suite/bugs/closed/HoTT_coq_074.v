Monomorphic Definition U1 := Type.
Monomorphic Definition U2 := Type.

Set Printing Universes.
Definition foo : True.
let t1 := type of U1 in
let t2 := type of U2 in
idtac t1 t2;
pose (t1 : t2). exact I. 
Defined.
