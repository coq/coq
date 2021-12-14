Local Notation foo := (forall x y:Type , x * y).

Set Mangle Names.
Local Notation goal  := foo.

Check eq_refl : eq foo goal.
