(* An example with constr subentries *)

Notation "[ x ]" := x (x custom myconstr at level 6).
Notation "x + y" := (Nat.add x y) (in custom myconstr, at level 5) : nat_scope.
Notation "x * y" := (Nat.mul x y) (in custom myconstr, at level 4) : nat_scope.
Notation "< x >" := x (in custom myconstr, at level 3, x constr at level 10).
Check [ < 0 > + < 1 > * < 2 >].

Notation "[ x ]" := x (x custom myconstr at level 6).
Notation "<< x >>" := x (in custom myconstr, at level 3, x custom anotherconstr at level 10).
Notation "# x" := (Some x) (in custom anotherconstr, at level 8, x constr at level 9).
Check [ << # 0 >> ].
