Module Type SIG.
  Axiom A : Set.
End SIG.

Module M0.
  Definition A : Set.
  exact nat.
  Qed.
End M0.

Module M1 : SIG.
  Definition A := nat.
End M1.

Module M2 <: SIG.
  Definition A := nat.
End M2.

Module M3 := M0.

Module M4 : SIG := M0.

Module M5 <: SIG := M0.


Module F (X: SIG) := X.


Module Type T.

  Module M0.
    Axiom A : Set.
  End M0.

  Declare Module M1: SIG.

  Module M2 <: SIG.
    Definition A := nat.
  End M2.

  Module M3 := M0.

  Module M4 : SIG := M0.

  Module M5 <: SIG := M0.

  Module M6 := F M0.

End T.
