Reset Initial.

Modtype SET.
  Axiom T:Set.
  Axiom x:T.
EndT SET.
 
Implicit Arguments On.

Mod M[X:SET].
  Definition T := nat.
  Definition x := O.
  Definition f := [A:Set][x:A]X.x.
EndM M.

Mod N:=M.

Mod Nat.
  Definition T := nat.
  Definition x := O.
EndM Nat.

Mod Z:=(N Nat).

Check (Z.f O).

Mod P[Y:SET] := N.

Mod Y:=P Z Nat.

Check (Y.f O).




