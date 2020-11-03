Ltac a _ := intro.
Ltac b := a ().
Goal True.
b.
Abort.
