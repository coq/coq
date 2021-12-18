Module Type T. Axiom U : Type. End T.
Module Type S. Declare Module B : T. End S.
Module Type S' (X : T). Axiom U' : Type. End S'.
Module Type M. Declare Module A : S. Declare Module A' : S'. End M.
Fail Module Type N := M with Definition A.B.V := nat.
Fail Module Type N := M with Definition A.C.U := nat.
Fail Module Type N := M with Definition V := nat.
Fail Module Type N := M with Definition A'.U' := nat.

Module M1. Axiom T : Type. End M1.
Module M2. Axiom T : Type. End M2.
Module Type V. Module N := M1. End V.
Fail Module Q : V with Module N := M2.
