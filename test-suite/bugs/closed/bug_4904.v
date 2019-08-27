Module A.
Module B.
Notation mynat := nat.
Notation nat := nat.
End B.
End A.

Print Term A.B.nat. (* Notation A.B.nat := nat *)
Import A.
Print Term B.mynat.
Print Term B.nat.
