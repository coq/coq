Module M.
  Definition T := nat.
  Definition x : T := 0.
End M.

Module Type SIG.
  Module M := Top.M.
  Module Type SIG.
    Parameter T : Set.
  End SIG.
  Declare Module N: SIG.
End SIG.

Module Z.
  Module M := Top.M.
  Module Type SIG.
    Parameter T : Set.
  End SIG.
  Module N := M.
End Z.

Module A : SIG := Z.
