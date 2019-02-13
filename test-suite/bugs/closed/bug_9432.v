
Record foo := { f : Type }.

Fail Canonical Structure xx@{} := {| f := Type |}.

Canonical Structure xx@{i} := {| f := Type@{i} |}.

Fail Coercion cc@{} := fun x : Type => Build_foo x.

Polymorphic Coercion cc@{i} := fun x : Type@{i} => Build_foo x.

Coercion cc1@{i} := (cc@{i}).
