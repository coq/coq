Inductive List (A : Set) : Set :=
  | Nil : List A
  | Cons : A -> List A -> List A.

Fail Type match Nil nat return nat with
     | b => b
     | Cons _ _ _ as d => d
     end.
