Reset Initial.

Module Type SET.
  Axiom T:Set.
  Axiom x:T.
End SET.
 
Implicit Arguments On.

Module M[X:SET].
  Definition T := nat.
  Definition x := O.
  Definition f := [A:Set][x:A]X.x.
End M.

Module N:=M.

Module Nat.
  Definition T := nat.
  Definition x := O.
End Nat.

Module Z:=(N Nat).

Check (Z.f O).

Module P[Y:SET] := N.

Module Y:=P Z Nat.

Check (Y.f O).




