Module M.
  Module Type SIG.
    Definition T:Set.
    Definition x:T.
  End SIG.
  Module N:SIG.
    Definition T:=nat.
    Definition x:=O.
  End N.
End M.

Module N:=M.

Module Type SPRYT.
  Module N.
    Definition T:=M.N.T.
    Definition x:T.
  End N.
End SPRYT.

Module K:SPRYT:=N.  
Module K':SPRYT:=M.  

Module Type SIG.
  Definition T:Set:=M.N.T.
  Definition x:T.
End SIG.

Module J:SIG:=M.N.
