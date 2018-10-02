Module Type TITI.
Parameter B:Set.
Parameter x:B.
Inductive A:Set:=
a1:B->A.
Definition f2: A ->B
:= fun (a:A) =>
match a with
 (a1 b)=>b
end.
Definition f: A -> B:=fun (a:A) => x.
End TITI.


Module Type TIT.
Declare Module t:TITI.
End TIT.

Module Seq(titi:TIT).
Module t:=titi.t.
Inductive toto:t.A->t.B->Set:=
t1:forall (a:t.A), (toto a (t.f a))
| t2:forall (a:t.A), (toto a (t.f2 a)).
End Seq.

Module koko(tit:TIT).
Module seq:=Seq tit.
Module t':=tit.t.

Definition def:forall (a:t'.A), (seq.toto a (t'.f a)).
intro ; constructor 1.
Defined.

Definition def2: forall (a:t'.A), (seq.toto a (t'.f2 a)).
intro; constructor 2.
(*  Toplevel input, characters 0-13
  constructor 2.
  ^^^^^^^^^^^^^
Error: Impossible to unify (seq.toto ?3 (seq.t.f2 ?3)) with
 (seq.toto a (t'.f2 a)).*)
