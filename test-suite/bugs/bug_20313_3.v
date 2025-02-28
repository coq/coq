Module Ltac1.
Notation boz y := ltac:(exact y) (only parsing).

Notation biz z := (boz (boz z)) (only parsing).

Check biz 0.

End Ltac1.

Require Import Ltac2.Ltac2.

Module Ltac2.
Notation boz y := ltac2:(exact $preterm:y) (only parsing).

Notation biz z := (boz (boz z)) (only parsing).

Check biz 0.

End Ltac2.
