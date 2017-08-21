Class C (A : Type) := c : A -> Type.

Record Inhab (A : Type) := { witness : A }. 

Instance inhab_C : C Type := Inhab.

Variable full : forall A (X : C A), forall x : A, c x.

Definition truc {A : Type} : Inhab A := (full _ _ _).
