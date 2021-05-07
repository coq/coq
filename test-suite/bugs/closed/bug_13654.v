Module dfrac.
  Declare Custom Entry dfrac.
End dfrac.

Module M1.
  Import dfrac.
  Notation "↦∗ dq" := (id dq) (at level 20, dq custom dfrac at level 1).
End M1.
Import M1.
