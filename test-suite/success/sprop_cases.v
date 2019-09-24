
Set Allow StrictProp.
Unset Elaboration StrictProp Cumulativity.

Definition foo (P:SProp) (x:False) := match x return P with end.
