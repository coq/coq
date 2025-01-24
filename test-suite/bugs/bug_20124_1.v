Module Type MiniOrderedType.
  Parameter Inline t : Type.
End MiniOrderedType.

Module Type L_Struct.
  Declare Module FOrd : MiniOrderedType.
End L_Struct.

Module Type ST_Struct.
  Declare Module L : L_Struct.
End ST_Struct.

Module CP_beta_eta (L_ : L_Struct).
  Module L := L_.
End CP_beta_eta.

Module Make (ST : ST_Struct) (CP : ST_Struct with Module L := ST.L).

End Make.

Declare Module ST : ST_Struct.
Module CP := CP_beta_eta ST.L.
Module SN := Make ST CP.
