From Coq Require Import PArith.
Local Open Scope positive_scope.
Goal Pos.add 3 3 = 1.
cbn [Pos.add Pos.add_carry Pos.succ]. (* There was a problem with canonical names *)
match goal with [ |- 6 = 1 ] => idtac end.
Abort.
