Module Type T.
#[warning="context-outside-section"] Context {A:Type}.
End T.

Module M(X:T).
  Import X.
  Check X.A.
  Check A.
  Definition B := A.
End M.
