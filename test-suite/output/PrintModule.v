Module FOO.

Module M.
 Definition T := nat.
End M.

Module Type S.
 Parameter T : Set.
End S.

Module N : S with Definition T := nat := M.

Print Module N.

End FOO.

Module BAR.

Module K. End K.
Module Type KS. End KS.

Module M.
 Module T := K.
End M.

Module Type S.
 Declare Module T : KS.
End S.

Module N : S with Module T := K := M.

Print Module N.

End BAR.
