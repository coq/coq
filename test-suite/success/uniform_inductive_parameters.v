Set Uniform Inductive Parameters.

Inductive list (A : Type) :=
  | nil : list
  | cons : A -> list -> list.
Check (list : Type -> Type).
Check (cons : forall A, A -> list A -> list A).

Inductive list2 (A : Type) (A' := prod A A) :=
  | nil2 : list2
  | cons2 : A' -> list2 -> list2.
Check (list2 : Type -> Type).
Check (cons2 : forall A (A' := prod A A), A' -> list2 A -> list2 A).
