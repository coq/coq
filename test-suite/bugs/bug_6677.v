Set Universe Polymorphism.

Definition T@{i} := Type@{i}.
Fail Definition U@{i} := (T@{i} <: Type@{i}).
Fail Definition eqU@{i j} : @eq T@{j} U@{i} T@{i} := eq_refl.
