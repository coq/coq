
Inductive foo : Type := .

Fail Check foo : Prop.

Inductive bar := .

Check bar : Prop.

Inductive baz := Baz (_:True) (_:baz).

Check baz : Prop.
