(* A few tests to check Argument Scope Global command *)

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
Arguments Scope Global negb'' [ _ ].
Arguments Scope Global negb' [ _ ].
Arguments Scope Global negb [ _ ].
Arguments Scope Global a [ _ ].
Arguments Scope Global b [ _ ].
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
