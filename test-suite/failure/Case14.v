Inductive List (A : Set) : Set :=
  | Nil : List A
  | Cons : A -> List A -> List A.

Definition NIL := Nil nat.
Fail Type match Nil nat return (List nat) with
     | NIL => NIL
     | _ => NIL
     end.
