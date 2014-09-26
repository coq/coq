Fail Inductive list (A : Type) (T := A) : Type :=
    nil : list A | cons : T -> list T -> list A.
