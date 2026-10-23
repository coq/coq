Module Type EmptyT.
End EmptyT.

Module EmptyM : EmptyT.
  Axiom in_empty : Prop.
End EmptyM.

Module F(A:EmptyT).
  Axiom in_f : Prop.
End F.

Module App := F EmptyM.

Module Type WithParam.
  Parameter param : Prop.
End WithParam.

Declare Module Declared : WithParam.

Module Implemented : WithParam.
  Definition param := True.
End Implemented.
