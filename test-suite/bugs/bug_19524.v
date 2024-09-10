
Set Warnings "+no-template-universe".
Fail #[universes(template)]
Inductive foo@{i} (A:Type@{i}) : Type@{i} -> Type@{i} := .

Inductive foo@{i} (A:Type@{i}) : Type@{i} -> Type@{i} := .

Fail Check foo True True : Prop.
Fail Check foo nat nat : Set.
