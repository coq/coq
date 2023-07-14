Set Printing Parentheses.

Module Constr.
Parameters x y z : nat.
Notation "a `+ b" := (a + b) (at level 50, b at level 50, left associativity).
Check (x `+ y `+ z).
End Constr.

Module CustomGlobal.
Declare Custom Entry foo.
Notation "a `+ b" := (a + b) (in custom foo at level 50, b at level 50).
Notation "x" := x  (in custom foo at level 0, x global).
Notation "( x )" := x  (in custom foo at level 0).
Notation "[ a ]" := a (a custom foo).
Parameters x y z : nat.
Check [x `+ y `+ z].
Check fun x y z => [x `+ y `+ z].
End CustomGlobal.

Module CustomIdent.
Declare Custom Entry bar.
Notation "a `+ b" := (a + b) (in custom bar at level 50, b at level 50).
Notation "x" := x  (in custom bar at level 0, x ident).
Notation "( x )" := x  (in custom bar at level 0).
Notation "[ a ]" := a (a custom bar).
Check fun x y z => [x `+ y `+ z].
End CustomIdent.
