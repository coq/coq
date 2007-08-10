Module Type T.

Parameter A : Type.

Inductive L : Type :=
| L0 : L (* without this constructor, it works right *)
| L1 :  A -> L.

End T.

Axiom Tp : Type.

Module TT : T.

Definition A : Type := Tp.

Inductive L : Type :=
| L0 : L
| L1 :  A -> L.

End TT.

