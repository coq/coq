(* It is forbidden to erase a variable (or a local def) that is used in
   the current goal. *)
Section S.
Let a := 0.
Definition b := a.
Goal b = b.
Fail clear a.
