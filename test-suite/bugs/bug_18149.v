Set Universe Polymorphism.
Unset Universe Minimization ToSet.


Cumulative Class A@{+i} := { a : Type@{i} }.

Local Instance Anat@{} : A@{Set} := { a := nat }.

Definition Anat1@{u|} : A@{u} := Anat.

Definition Anat2@{u|} : A@{u} := _.
