Module Type S1.
  Parameter t : Type.
End S1.

Module Type S2.
  Parameter t : Type.
End S2.

Module F (M1 M2 : S2).
End F.

Module Type S.
End S.

Module F1 (M1 M2 : S).
Print F. (* Cannot mask the absolute name "M3.t"! *)
End F1.
