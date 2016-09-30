Module A.
Module B.
Notation mynat := nat.
Notation nat := nat.
End B.
End A.

Print A.B.nat. (* Notation A.B.nat := nat *)
Import A.
Print B.mynat.
Print B.nat.
