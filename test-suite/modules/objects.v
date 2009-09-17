Module Type SET.
  Axiom T : Set.
  Axiom x : T.
End SET.

Set Implicit Arguments.
Unset Strict Implicit.

Module M (X: SET).
  Definition T := nat.
  Definition x := 0.
  Definition f (A : Set) (x : A) := X.x.
End M.

Module N := M.

Module Nat.
  Definition T := nat.
  Definition x := 0.
End Nat.

Module Z := N Nat.

Check (Z.f 0).

Module P (Y: SET) := N.

Module Y := P Z Nat.

Check (Y.f 0).



