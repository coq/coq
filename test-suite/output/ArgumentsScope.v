(* A few tests to check Global Argument Scope command *)

Section A.
Variable a : bool -> bool.
Definition negb' := negb.
Section B.
Variable b : bool -> bool.
Definition negb'' := negb.
About a.
About b.
About negb''.
About negb'.
About negb.
Global Arguments negb'' _ : clear scopes.
Global Arguments negb' _ : clear scopes.
Global Arguments negb _ : clear scopes.
Global Arguments a _ : clear scopes.
Global Arguments b _ : clear scopes.
About a.
About b.
About negb.
About negb'.
About negb''.
End B.
About a.
End A.
About negb.
About negb'.
About negb''.
