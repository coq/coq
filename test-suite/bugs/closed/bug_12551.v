
Section S.
  Context [A:Type] (a:A).
  Definition id := a.
End S.

Check id : forall A, A -> A.
Check id 0 : nat.
