Module M.
  Definition t:=nat.
  Definition x:=O.
End M.

Print M.t.


Module Type SIG.
  Parameter t:Set.
  Parameter x:t.
End SIG.


Module F[X:SIG].
  Definition t:=X.t->X.t.
  Definition x:t.
    Intro.
    Exact X.x.
  Defined.
  Definition y:=X.x.
End F.


Module N := F M.

Print N.t.
Eval Compute in N.t.


Module N' : SIG := N.

Print N'.t.
Eval Compute in N'.t.


Module N'' <: SIG := F N.

Print N''.t.
Eval Compute in N''.t.

Eval Compute in N''.x.


Module N''' : SIG with Definition t:=nat->nat  :=  N.

Print N'''.t.
Eval Compute in N'''.t.

Print N'''.x.


Import N'''.

Print t.