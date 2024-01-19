Module Type SIG.
End SIG.

Fail Module Import A (S:SIG).

Module Type F(X:SIG). End F.

Fail Declare Module Import M : F.

Declare Module M : F.

Fail Module Import N := M.
