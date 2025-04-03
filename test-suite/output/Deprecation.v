#[deprecated(since = "X.Y", note = "Use idtac instead.")]
 Ltac foo := idtac.

Fail #[deprecated(since="today", why="I said so")] Definition foo := 1.

Goal True.
foo.
Abort.

Set Warnings "-deprecated-since-X.Y".

Goal True.
foo.
Abort.

Set Warnings "+deprecated-since-X.Y".

Goal True.
Fail foo.
Abort.

#[deprecated(since = "library X.Y", note = "Use baz instead.")]
 Ltac bar := idtac.

Goal True.
bar.
Abort.

#[warn(note="hello")] Definition bar := 2.

Check bar.

#[warn(note="use less +s", cats="too many plus,fragile")] Notation "x +++ y" := (x + y) (at level 2).
#[warn(note="use less +s 2", cats="too-many-plus")] Notation "x ++ y" := (x + y).

Check 1 +++ 2.
Check 1 ++ 2.
