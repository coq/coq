Goal exists I, I = Logic.I.
Show.
Abort.

Notation f x y p q r := ((forall x, p /\ r) /\ forall y, q /\ r).
Goal f True False True False (Logic.True /\ Logic.False).
Show.
Abort.

Notation "[ x | y ; z ; .. ; t ]" := (pair .. (pair (forall x, y) (forall x, z)) .. (forall x, t)).
Goal [ I | I = Logic.I ; I = Logic.I ] = [ I | I = Logic.I ; I = Logic.I ].
Show.
Abort.

Notation "[ x & p | y ; .. ; z ; t ]" := (forall x, p -> y -> .. (forall x, p -> z -> forall x, p -> t) ..).
Goal [ I & I = Logic.I | I = Logic.I ; Logic.I = I ].
Show.
Abort.
