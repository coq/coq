Set Universe Polymorphism.

(** Here we assume the universe is irrelevant after first argument application... *)
Axiom M : Type -> Prop.
Axiom raise : forall {T : Type}, M T.

Inductive goal : Type :=
| AHyp : forall {A : Type}, goal.

(** u is invariant but u0 is not as it is determined by M's first artument unit *)
Definition gtactic@{u u0} := goal@{u} -> M@{u0} (unit).
Class Seq (C : Type) := seq : C -> gtactic.
Arguments seq {C _} _.

#[export] Instance seq_one :  Seq@{Set _ _} (gtactic) := fun t2 => fun g => raise.

Definition x1 : gtactic := @seq@{_ _ _} _ _ (fun g : goal => raise).
Definition x2 : gtactic := @seq@{_ _ _} _ seq_one (fun g : goal => raise).
