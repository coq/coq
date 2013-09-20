Inductive List (A : Set) : Set :=
  | Nil : List A
  | Cons : A -> List A -> List A.

Fail Type
  (fun l : List nat =>
   match l return nat with
   | Nil nat => 0
   | Cons a l => S a
   end).
