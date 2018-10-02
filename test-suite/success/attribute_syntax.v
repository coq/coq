From Coq Require Program.Wf.

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
Reset f.

#[deprecated(since="8.9.0")]
Ltac foo := foo.

Module M.
  #[local] #[polymorphic] Definition zed := Type.

  #[local, polymorphic] Definition kats := Type.
End M.
Check M.zed@{_}.
Fail Check zed.
Check M.kats@{_}.
Fail Check kats.
