Ltac a _ := pose (I : I).
Ltac b _ := a ().
Ltac abs _ := abstract b ().
Ltac c _ := abs ().
Goal True.
  Fail c ().
Abort.
