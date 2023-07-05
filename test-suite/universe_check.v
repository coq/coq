Set Universe Polymorphism.
(* So that by default we only get Set <= a constraints, not Set < a *)
Set Debug "loop-checking".
Set Debug "loop-checking-loop".
(* Set Debug "loop-checking-model".*)
(* a = 0
      b -> c
      a -> b + 1
      c -> c + 1

      1st round: b = 0.
      W = {b}
      2nd round: c = 0.
      W = {b, c}
      c = 1.
      W = {b, c}
      *)
(* Section test_loop.
  Universes a b c d.
  Constraint b < a.
  Constraint c <= d.
  Constraint d < c.
  Fail Constraint b < a. *)

Section funext.
  Universes a b c d.

  Constraint Set < a.
  Constraint b < a.
  Constraint Set < c.
  Constraint c < b.
  Constraint d <= a.

  Check Constraint d <= a.
End funext.

Section test_loop.
  Universes a b.
  Constraint a < b.
  Fail Check Constraint b < a.
  Fail Constraint b < a.
End test_loop.

Section test.
Universes a b c d.

Constraint a < b.
Constraint b < c.
Constraint c < d.

Check Constraint Set < b.

End test.

Section test2.
  Universes a b.
  Constraint a <= b.
  Fail Check Constraint a = b.

  Constraint b <= a.
  Check Constraint a = b.
End test2.

Section test3.
  Universes a b c d.
  Constraint a <= c.
  Constraint b <= c.
  Fail Check Constraint a <= b.
  Check Constraint a <= c.
  Constraint a <= d, d <= b.
  Check Constraint a <= b.

  Constraint b <= a.
  Check Constraint a = b, a = d.
End test3.
