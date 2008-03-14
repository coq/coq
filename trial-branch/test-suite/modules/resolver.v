Module Type TA.
Parameter t : Set.
End TA.

Module Type TB.
Declare Module A: TA.
End TB.

Module Type TC.
Declare Module B : TB.
End TC.

Module Type TD.

Declare Module B: TB .
Declare Module C: TC
   with Module B := B  .
End TD.

Module Type TE.
Declare Module D : TD.
End TE.

Module Type TF.
Declare Module E:  TE.
End TF.

Module G (D: TD).
Module B' := D.C.B.
End G.

Module H  (F: TF).
Module I := G(F.E.D).
End H.

Declare Module F:  TF.
Module K := H(F).
