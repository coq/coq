Section foo.
Variable f : forall n : nat, nat.
Arguments f {_}.
Check f (n := 3).
Global Arguments f {bar} : rename.
End foo.

Section foo.
Variable f : forall n : nat, nat.
Arguments f {_}.
Fail Check f (bar := 3).
End foo.
