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

Print Term TrM.A.
Print Term OpM.A.
Print Term TrM.B.
Print Term OpM.B.
