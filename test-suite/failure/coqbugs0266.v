(* It is forbidden to erase a variable (or a local def) that is used in
   the current goal. *)
Section S.
Local a:=O.
Definition b:=a.
Goal b=b.
Clear a.
