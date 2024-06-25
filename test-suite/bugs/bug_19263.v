Set Warnings "+no-template-universe".

Fail #[universes(template)]
Inductive sum@{u} (A B : Type@{u}) : Type := inl : A -> sum A B | inr : B -> sum A B.

#[universes(template)]
Inductive sum (A B : Type) : Type := inl : A -> sum A B | inr : B -> sum A B.
