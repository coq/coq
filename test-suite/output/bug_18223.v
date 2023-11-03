Declare Custom Entry foo.
Declare Custom Entry bar.

Parameter (A : Type).
Parameter (Q : A -> A -> A).
Parameter (P : A -> A).

Notation "< x >" := (P x) (x custom foo).
Notation "x y" := (Q x y)  (in custom bar at level 1, right associativity).
Notation "x" := x (in custom bar at level 0, x global).

Module Order1.
Notation "| x |" := (x) (x custom bar).
Notation "{ x }" := (x) (in custom foo, x constr).
Check (fun a b => < {Q b a} >).
End Order1.

Module Order2.
Notation "{ x }" := (x) (in custom foo, x constr).
Notation "| x |" := (x) (x custom bar).
Check (fun a b => < {Q b a} >).
End Order2.
