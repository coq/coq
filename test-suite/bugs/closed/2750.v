
Module Type ModWithRecord.

  Record foo : Type :=
  { A : nat
  ; B : nat
  }.
End ModWithRecord.

Module Test_ModWithRecord (M : ModWithRecord).

  Definition test1 : M.foo :=
    {| M.A := 0
     ; M.B := 2
     |}.

  Module B := M.

  Definition test2 : M.foo :=
    {| M.A := 0
     ; M.B := 2
     |}.
End Test_ModWithRecord.
