Implicit Arguments On.

Module Type SIG.
  Parameter id:(A:Set)A->A.
End SIG.
 
Module M[X:SIG].
  Definition idid := (X.id X.id).
  Definition id := (idid X.id).
End M.

Module N:=M.

Module Nat.
  Definition T := nat.
  Definition x := O.
  Definition id := [A:Set][x:A]x.
End Nat.

Module Z:=(N Nat).

Check (Z.idid O).

Module P[Y:SIG] := N.

Module Y:=P Nat Z.

Check (Y.id O).




