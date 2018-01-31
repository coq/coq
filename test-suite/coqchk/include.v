(* See https://github.com/coq/coq/issues/5747 *)
Module Type S.
End S.

Module N.
Inductive I := .
End N.

Module M : S.
  Include N.
End M.
