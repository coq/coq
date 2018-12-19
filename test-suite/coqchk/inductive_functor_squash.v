

Module Type T.
  Parameter f : nat -> Type.
End T.

Module F(A:T).
  Inductive ind : Prop :=
    C : A.f 0 -> ind.
End F.

Module A. Definition f (x:nat) := True. End A.

Module M := F A.
(* M.ind could eliminate into Set/Type even though F.ind can't *)
