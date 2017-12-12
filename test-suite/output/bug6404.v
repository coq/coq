Ltac a _ := pose (I : I).
Ltac b _ := a ().
Ltac abs _ := transparent_abstract b ().
Ltac c _ := abs ().
Goal True.
  Fail c ().
Abort.
