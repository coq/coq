Section Foo.
Variable A : Type.
Inductive I (n:nat) := { it : A }.
End Foo.
Fail Check fun x => x.(it). (* expect 2 arguments, shouldn't raise an anomaly *)
