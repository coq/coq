Inductive list (A : Set) : Set :=
  | nil : list A
  | cons : A -> list (A -> A) -> list A.

