
Notation foo := ltac:(exact 1).

Notation bar := (2 :> nat).

Notation baz := (3 <: nat).

Check foo.
Check bar.
Check baz.
