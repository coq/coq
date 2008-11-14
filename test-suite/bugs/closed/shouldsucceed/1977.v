Inductive T {A} : Prop := c : A -> T.
Goal (@T nat).
apply c. exact 0.
Qed.
