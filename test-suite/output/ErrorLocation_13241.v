Module Direct.
Ltac a := intro.
Ltac b := a.
Goal True.
Fail b.
Abort.
End Direct.

Module Thunked.
Ltac a _ := intro.
Ltac b := a ().
Goal True.
Fail b.
Abort.
End Thunked.
