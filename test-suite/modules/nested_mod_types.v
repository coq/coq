Module Type T.
  Module Type U.
    Module Type V.
      #[local] Parameter b : nat.
    End V.
    #[local] Parameter a : nat.
  End U.
  Declare Module u : U.
  Declare Module v : u.V.
End T.

Module F (t:T).
End F.

Module M:T.
  Module Type U.
    Module Type V.
      #[local] Parameter b : nat.
    End V.
     #[local] Parameter a : nat.
  End U.
  Declare Module u : U.
  Declare Module v : u.V.
End M.

Module FM := F M.
