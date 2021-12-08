Module Type T.
  Parameter b : Set.
End T.

Module M1(N : T).
End M1.

Module M2.
End M2.

Section S.
  Variable a : Set.
  Definition b := a.
  Fail Include M1.
End S.
