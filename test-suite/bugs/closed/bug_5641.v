Set Universe Polymorphism.

Definition foo@{i j} (A : Type@{i}) : Type@{j}.
Proof.
abstract (exact ltac:(abstract (exact A))).
Defined.
