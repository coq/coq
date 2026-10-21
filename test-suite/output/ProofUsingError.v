Section S.
  Context {A} (x y:A).

  Goal A * A.
  Proof using.
    exact (x,y).
    Fail Qed.
  Abort.

  Goal A * A.
  Proof using.
    exact (x,x).
    Fail Qed.
  Abort.

  Goal True.
  Proof using.
    exact (let _ := A in I).
    Fail Qed.
  Abort.
End S.
