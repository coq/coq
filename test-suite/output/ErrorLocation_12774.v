Ltac f := simpl.
Ltac g := auto; intro.

Goal Type.
Fail simpl; exact 0.
Fail f; exact 0.
Fail g.
Abort.
