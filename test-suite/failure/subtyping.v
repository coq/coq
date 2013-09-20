(* A variant of bug #1302 that must fail *)

Module Type T.

 Parameter A : Type.

 Inductive L : Prop :=
 | L0
 | L1 :  (A -> Prop) -> L.

End T.

Module TT : T.

 Parameter A : Type.

 Inductive L : Type :=
 | L0
 | L1 :  (A -> Prop) -> L.

Fail End TT.
