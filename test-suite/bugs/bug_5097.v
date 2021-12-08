(* Tracing existing evars along the weakening rule ("clear") *)
Goal forall y, exists x, x=0->x=y.
intros.
eexists ?[x].
intros.
let x:=constr:(ltac:(clear y; exact 0)) in idtac x.
Abort.
