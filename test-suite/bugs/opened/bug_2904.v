Module Type S.
Parameter t : Type.
Module M'.
Parameter t : Type.
Definition u := S.t.
End M'.
End S.

Module M : S.
Definition t := unit.
Module M'.
Definition t := bool.
Definition u := M.t.
End M'.
End M.

Require Extraction.
Fail Extraction TestCompile M.
