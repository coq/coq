Module A.
Set Primitive Projections.
Record foo := Foo { foo_n : nat }.
Notation "'■' x" := (foo_n x) (at level 50).
Check forall (f:foo), ■ f = ■ f.
End A.

Module A'.
Set Primitive Projections.
Record foo := Foo { foo_n : nat }.
Notation "'■' x" := x.(foo_n) (at level 50).
Check forall (f:foo), ■ f = ■ f.
End A'.

(* Variant with non-primitive projections *)

Module B.
Record T := {a:nat}.
Notation "%% x" := (a x) (at level 0, x at level 0).
Check fun x => %%x.
End B.

Module B'.
Record T := {a:nat}.
Notation "%% x" := x.(a) (at level 0, x at level 0).
Check fun x => %%x.
End B'.
