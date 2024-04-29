
Set Dependent Proposition Eliminators.

Inductive bar : Prop := XBAR | YBAR.

Check bar_ind : forall P : bar -> Prop, P XBAR -> P YBAR -> forall b : bar, P b.
