Ltac can_unfold x := let b := eval cbv delta [x] in x in idtac.
Definition i := O.
Goal False.
Fail can_unfold (i>0).
Abort.
