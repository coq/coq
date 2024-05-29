Set Warnings "+automatic-prop-lowering".

Fail Inductive foo : Type := .

Unset Automatic Proposition Inductives.

Inductive foo : Type := .

Fail Check foo : Prop.

Inductive bar := .

Check bar : Prop.

Inductive baz := Baz (_:True) (_:baz).

Check baz : Prop.
