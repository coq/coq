Module Type TIT.

Inductive X:Set:=
 b:X.
End TIT.


Module Type TOTO.
Declare Module t:TIT.
Inductive titi:Set:=
 a:t.X->titi.
End TOTO.


Module toto (ta:TOTO).
Module ti:=ta.t.

Definition ex1:forall (c d:ti.X), (ta.a d)=(ta.a c) -> d=c.
intros.
injection H.
