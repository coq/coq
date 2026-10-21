Module Type S.
  Parameter t : Type.
  Parameter x : t.
End S.

Module F (X : S).
  Parameter t : Type.
  Parameter x : t.
End F.

(* An unsuccessful attempt to print types must not silently omit them. *)
Print Module Type S.
Print Module F.

(* The existing warning controls can require typed output. *)
Set Warnings "+module-printing-fallback".
Fail Print Module Type S.

(* Requesting short output explicitly does not emit the warning. *)
Set Short Module Printing.
Print Module Type S.
Print Module F.
Unset Short Module Printing.

(* Successful rich printing remains quiet, even with the warning as an error. *)
Module M.
  Parameter t : Type.
  Parameter x : t.
End M.
Print Module M.
