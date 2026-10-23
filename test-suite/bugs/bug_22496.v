Reserved Notation "x == y"
  (at level 17, left associativity, y at level 16, only printing).
Notation "x == y" := (Nat.eqb x y)
  (at level 70, no associativity).
Check (0 == 1 + 1).

Set Warnings "+notation-incompatible-prefix".

Module SameLevels.
  Reserved Notation "'wrap' x" (at level 80, x at level 79, only printing).
  Notation "'wrap' x" := x (at level 80, x at level 79).
  Notation "'wrap' x 'tag'" := x.
  Check (wrap 1 + 1 tag).
End SameLevels.

Module DifferentLevels.
  Reserved Notation "'wrap' x" (at level 10, x at level 9, only printing).
  Notation "'wrap' x" := x (at level 80, x at level 79).
  Notation "'wrap' x 'tag'" := x.
  Check (wrap 1 + 1 tag).
End DifferentLevels.

Module ImportedParser.
  Reserved Notation "'wrap' x" (at level 10, x at level 9, only printing).
  Module Parser.
    Notation "'wrap' x" := x (at level 80, x at level 79).
  End Parser.
  Import Parser.
  Notation "'wrap' x 'tag'" := x.
  Check (wrap 1 + 1 tag).
End ImportedParser.
