Set Universe Polymorphism.

(** Here we assume the universe is irrelevant after first argument application... *)
Axiom M : Type -> Prop.
Axiom raise : forall {T}, M T.

Inductive goal : Type :=
| AHyp : forall {A : Type}, goal.

Definition gtactic@{u u0} := goal@{u} -> M@{u0} (False).

Class Seq (C : Type) :=
  seq : C -> gtactic.
Arguments seq {C _} _.

#[export] Instance seq_one : Seq@{Set _} (gtactic) := fun t2 => fun g => raise.

Definition x1 : gtactic := @seq@{_ _} _ _ (fun g : goal => raise).
Definition x2 : gtactic := @seq@{_ _} _ seq_one (fun g : goal => raise).
