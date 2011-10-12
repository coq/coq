Module Type T.
End T.

Declare Module K : T.

Module Type L.
Declare Module E : T.
End L.

Module M1 : L with Module E:=K.
Module E := K.
Fail Inductive t := E. (* Used to be accepted, but End M1 below was failing *)
End M1.

Module M2 : L with Module E:=K.
Inductive t := E.
Fail Module E := K. (* Used to be accepted *)
Fail End M2. (* Used to be accepted *)
