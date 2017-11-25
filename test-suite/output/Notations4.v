(* An example with constr subentries *)

Declare Custom Entry myconstr.

Notation "[ x ]" := x (x custom myconstr at level 6).
Notation "x + y" := (Nat.add x y) (in custom myconstr, at level 5).
Notation "x * y" := (Nat.mul x y) (in custom myconstr, at level 4).
Notation "< x >" := x (in custom myconstr, at level 3, x constr at level 10).
Check [ < 0 > + < 1 > * < 2 >].

Declare Custom Entry anotherconstr.

Notation "[ x ]" := x (x custom myconstr at level 6).
Notation "<< x >>" := x (in custom myconstr, at level 3, x custom anotherconstr at level 10).
Notation "# x" := (Some x) (in custom anotherconstr, at level 8, x constr at level 9).
Check [ << # 0 >> ].
