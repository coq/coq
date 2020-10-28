Require Import ssreflect.

Ltac t1 x := replace (x x) with (x x).
Print t1.

Ltac t2 x := case: x.
Print t2.

Ltac t3 := by move->.
Print t3.

Ltac t4 := congr True.
Print t4.
