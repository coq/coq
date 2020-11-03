(* Check that rules with patterns are not registered for cases patterns *)
Module PrintingTest.
Declare Custom Entry test.
Notation "& x" := (Some x) (in custom test at level 0, x pattern).
Check fun x => match x with | None => None | Some tt => Some tt end.
Notation "& x" := (Some x) (at level 0, x pattern).
Check fun x => match x with | None => None | Some tt => Some tt end.
End PrintingTest.

Fail Notation "x &" := (Some x) (at level 0, x pattern).
