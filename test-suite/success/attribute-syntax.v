From Coq Require Program.

Section Scope.

#[local] Coercion nat_of_bool (b: bool) : nat :=
  if b then 0 else 1.

Check (refl_equal : true = 0 :> nat).

End Scope.

Fail Check 0 = true :> nat.

#[polymorphic]
Definition ι T (x: T) := x.

Check ι _ ι.

#[program]
Fixpoint f (n: nat) {wf lt n} : nat := _.

#[deprecated(since="8.9.0")]
Ltac foo := foo.
