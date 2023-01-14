Module Example2.

Notation "'foobar'" := 1.
Definition a := foobar.
Definition A := 2.
Fail Definition b := foobarA.
Notation "'\foobar'" := (fun x => 1 + x).
Fail Definition b := \foobarA.

End Example2.
