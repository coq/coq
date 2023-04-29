Disable Notation "x + y" := (Nat.add x y).

Declare Custom Entry foo.
Notation "x * y" := (Nat.mul x y) (in custom foo at level 0).
Fail Disable Notation "x * y" := (Nat.mul x y). (* need flag all *)
Disable Notation "x * y" := (Nat.mul x y) (all).
Enable Notation := (Nat.mul _ _) : nat_scope.

Disable Notation := ex2 (all).
Disable Notation "<=" (all).
Disable Notation (all) : nat_scope.
Fail Disable Notation.

Module Abbrev.
Fail Disable Notation f. (* no abbreviation with such suffix *)
Notation f w := (S w).
Disable Notation f w := (S w).
Enable Notation := (S _).

Module A. Notation a := Prop. End A. Include A.
Disable Notation A.a.
Check a.
Disable Notation a.
Fail Check a.
Check Prop.
Enable Notation a (all). (* Note: reactivation is not necessarily in the same order as it was earlier *)
Check a.
Check Prop.

Module Shadowed. Notation x := true. End Shadowed.
Import Shadowed.
Notation x := 0.
Check x.
Disable Notation Abbrev.x.
Check x.
Enable Notation x.
Check x.

End Abbrev.
