Implicit Arguments On.

Modtype SIG.
  Parameter id:(A:Set)A->A.
EndT SIG.
 
Mod M[X:SIG].
  Definition idid := (X.id X.id).
  Definition id := (idid X.id).
EndM M.

Mod N:=M.

Mod Nat.
  Definition T := nat.
  Definition x := O.
  Definition id := [A:Set][x:A]x.
EndM Nat.

Mod Z:=(N Nat).

Check (Z.idid O).

Mod P[Y:SIG] := N.

Mod Y:=P Nat Z.

Check (Y.id O).




