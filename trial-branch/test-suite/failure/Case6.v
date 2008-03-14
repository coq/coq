Inductive List (A : Set) : Set :=
  | Nil : List A
  | Cons : A -> List A -> List A.

Type (match Nil nat return List nat with
      | NIL   => NIL
      | (CONS _ _)  => NIL
      end).
