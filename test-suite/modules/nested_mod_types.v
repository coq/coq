Module Type T.
  Module Type U.
    Module Type V.
      Variable b : nat.
    End V.
    Variable a : nat.
  End U.
  Declare Module u : U.
  Declare Module v : u.V.
End T.

Module F (t:T).
End F.

Module M:T.
  Module Type U.
    Module Type V.
      Variable b : nat.
    End V.
    Variable a : nat.
  End U.
  Declare Module u : U.
  Declare Module v : u.V.
End M.

Module FM := F M.
