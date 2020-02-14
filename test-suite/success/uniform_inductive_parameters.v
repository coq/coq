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

Inductive list3 | A := nil3 | cons3 : A -> list3 (A * A)%type -> list3 A.

Unset Uniform Inductive Parameters.

Inductive list4 A | := nil4 | cons4 : A -> list4 -> list4.

Inductive Acc {A:Type} (R:A->A->Prop) | (x:A) : Prop
  := Acc_in : (forall y, R y x -> Acc y) -> Acc x.
