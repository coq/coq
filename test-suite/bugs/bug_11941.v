Inductive Box A := box (_:A).
Inductive unit := tt.
Definition t := unit.
Record foo := { bar : Box t }.
Fail Scheme Equality for foo.
