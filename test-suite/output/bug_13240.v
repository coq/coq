Require Import ssreflect.

Ltac t1 a b := a; last b.
Print t1.

Ltac t2 := do !idtac.
Print t2.

Ltac t3 := idtac => True.
Print t3.
