Module Type SIG.
  Inductive w:Set:=A:w.
  Parameter f : w->w.
End SIG.

Module M:SIG.
  Inductive w:Set:=A:w.
  Definition f:=[x]Cases x of A => A end.
End M.

Module N:=M.

Check (N.f M.A).
