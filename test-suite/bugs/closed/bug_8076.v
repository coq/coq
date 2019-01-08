
Notation leak a := ltac:(let x := constr:(Type) in exact a) (only parsing).
Record foo@{} (P:leak Prop) := { f : leak Prop }.
