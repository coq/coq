Module M.
  Definition T:=nat.
  Definition x:T:=O.
End M.

Module Type SIG.
  Module M:=Top.M.
  Module Type SIG.
    Definition T:Set.
  End SIG.
  Module N:SIG.
End SIG.

Module Z.
  Module M:=Top.M.
  Module Type SIG.
    Definition T:Set.
  End SIG.
  Module N:=M.
End Z.

Module A:SIG:=Z.  
