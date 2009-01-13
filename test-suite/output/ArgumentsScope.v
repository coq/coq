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
Global Arguments Scope negb'' [ _ ].
Global Arguments Scope negb' [ _ ].
Global Arguments Scope negb [ _ ].
Global Arguments Scope a [ _ ].
Global Arguments Scope b [ _ ].
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
