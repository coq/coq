Module M.
  Definition t := nat.
  Definition x := 0.
End M.

Print Term M.t.


Module Type SIG.
  Parameter t : Set.
  Parameter x : t.
End SIG.


Module F (X: SIG).
  Definition t := X.t -> X.t.
  Definition x : t.
    intro.
    exact X.x.
  Defined.
  Definition y := X.x.
End F.


Module N := F M.

Print Term N.t.
Eval compute in N.t.


Module N' : SIG := N.

Print Term N'.t.
Eval compute in N'.t.


Module N'' <: SIG := F N.

Print Term N''.t.
Eval compute in N''.t.

Eval compute in N''.x.


Module N''' : SIG with Definition t := nat -> nat := N.

Print Term N'''.t.
Eval compute in N'''.t.

Print Term N'''.x.


Import N'''.

Print Term t.
