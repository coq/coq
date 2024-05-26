Declare Custom Entry mor.
Declare Custom Entry obj.
Notation "< x >" := (x) (x custom mor).
Notation "x" := x (in custom mor at level 0, x global).
Notation "x" := x (in custom obj at level 0, x global).
Parameter C : Type.
Parameters a b c : C.
Parameter op3 : C -> C ->  C.
Notation "x ++ y" := (op3 x y)  (y custom obj, in custom mor at level 40, left associativity).
Check (< a ++ b ++ c >).
