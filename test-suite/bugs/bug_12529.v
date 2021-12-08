Goal SProp.
match goal with |- SProp => idtac end.
Fail match goal with |- Prop => idtac end.
Abort.

Goal Prop.
Fail match goal with |- SProp => idtac end.
match goal with |- Prop => idtac end.
Abort.

Class F A := f : A.

Inductive pFalse : Prop  := .
Inductive sFalse : SProp := .

Hint Extern 0 (F Prop) => exact pFalse : typeclass_instances.
Definition pf := f : Prop.

Hint Extern 0 (F SProp) => exact sFalse : typeclass_instances.
Definition sf := (f : SProp).
Definition pf' := (f : Prop).
