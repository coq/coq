(* Was failing while building the _rect scheme, due to wrong computation of *)
(* the number of non recursively uniform parameters in the presence of let-ins*)
Inductive list (A : Type) (T := A) : Type :=
    nil : list A | cons : T -> list T -> list A.
