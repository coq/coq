Module N.
Definition f := plus.
(* <Warning> : Syntax is discontinued *)
Check (f 0 0).
End N.
Check (N.f 0 0).
Import N.
Check (f 0 0).
Check (f 0 0).
Module M := N.
Check (f 0 0).
Check (f 0 0).
Import M.
Check (f 0 0).
Check (N.f 0 0).
