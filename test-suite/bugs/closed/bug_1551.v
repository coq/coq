Module Type S.
  Parameter empty: Set.
End S.

Module D (M:S).
  Import M.
  Definition empty:=nat.
End D.

Module D' (M:S).
  Import M.
  Definition empty:Set. exact nat. Qed.
End D'.
