Inductive List (A : Set) : Set :=
  | Nil : List A
  | Cons : A -> List A -> List A.

Type match Nil nat return nat with
     | b => b
     | Cons _ _ _ as d => d
     end.
