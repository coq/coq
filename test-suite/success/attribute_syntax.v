From Coq Require Program.Wf.

Section Scope.

#[local] Coercion nat_of_bool (b: bool) : nat :=
  if b then 0 else 1.

Check (refl_equal : true = 0 :> nat).

End Scope.

Fail Check 0 = true :> nat.

#[universes(polymorphic)]
Definition ι T (x: T) := x.

Check ι _ ι.

#[universes(polymorphic=no)]
Definition ιι T (x: T) := x.

Fail Check ιι _ ιι.

#[program]
Fixpoint f (n: nat) {wf lt n} : nat := _.
Next Obligation. Admitted.

#[program=yes]
Fixpoint f1 (n: nat) {wf lt n} : nat := _.
Next Obligation. Admitted.

#[deprecated(since="8.9.0")]
Ltac foo := foo.

Module M.
  #[local] #[universes(polymorphic)] Definition zed := Type.

  #[local, universes(polymorphic)] Definition kats := Type.
End M.
Check M.zed@{_}.
Fail Check zed.
Check M.kats@{_}.
Fail Check kats.

Export Set Foo.

#[ export ] Set Foo.

Fail #[ export ] Export Foo.
(* Attribute for Locality specified twice *)

(* Tests for deprecated attribute syntax *)
Set Warnings "-deprecated-attribute-syntax".

#[program=yes]
Fixpoint f2 (n: nat) {wf lt n} : nat := _.
Next Obligation. Admitted.

#[universes(polymorphic=no)]
Definition ιιι T (x: T) := x.
Fail Check ιιι _ ιιι.
