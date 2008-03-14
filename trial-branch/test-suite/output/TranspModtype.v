Module Type SIG.
  Axiom A : Set.
  Axiom B : Set.
End SIG.

Module M : SIG.
  Definition A := nat.
  Definition B := nat.
End M.

Module N <: SIG := M.

Module TranspId (X: SIG) <: SIG with Definition A := X.A := X.
Module OpaqueId (X: SIG) : SIG with Definition A := X.A := X.

Module TrM := TranspId M.
Module OpM := OpaqueId M.

Print TrM.A.
Print OpM.A.
Print TrM.B.
Print OpM.B.
