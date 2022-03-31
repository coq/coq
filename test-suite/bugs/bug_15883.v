Module Type S.
Definition T := nat.
Parameter n : T.
End S.

Module Type S'.
Definition T := nat.
Parameter n : nat.
End S'.

Module Type F(X : S).
End F.

Module K (X : S').
End K.

Module R : F := K.
