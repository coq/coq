Ltac can_unfold x := let b := eval cbv delta [x] in x in idtac.
Definition i := O.
Goal False.
can_unfold (i>0).
Abort.
