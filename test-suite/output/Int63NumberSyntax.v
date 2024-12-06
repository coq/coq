Require Import PrimInt63.

Check 2%uint63.
Open Scope uint63_scope.
Check 2.
Check 9223372036854775807.
Check 0x1ab.
Check 0X1ab.
Check 0x1Ab.
Check 0x1aB.
Check 0x1AB.
Fail Check 0x1ap5.  (* exponents not implemented (yet?) *)
Fail Check 0x1aP5.
Check 0x0.
Check 0x000.
Fail Check 0xg.
Fail Check 0xG.
Fail Check 00x1.
Fail Check 0x.
Check (PrimInt63.add 2 2).
Fail Check -1.
Fail Check 9223372036854775808.

Set Printing All.
Check 1%uint63.
Unset Printing All.

Open Scope nat_scope.
Check 2. (* : nat *)
Check 2%uint63.
Delimit Scope uint63_scope with ui63.
Definition t := 2%uint63.
Print t.
Delimit Scope nat_scope with uint63.
Print t.
Check 2.
Close Scope nat_scope.
Check 2.
Close Scope uint63_scope.

Check add 2 2.
Open Scope uint63_scope.
Check (add 2 2).
Eval vm_compute in add 2 2.
Eval vm_compute in mul 65675757 565675998.

Eval simpl in add 2 2.
Eval hnf in add 2 2.
Eval cbn in add 2 2.
Eval hnf in PrimInt63.add.

Eval simpl in add (mul 2 3) (mul 2 3).
Eval hnf in add (mul 2 3) (mul 2 3).
Eval cbn in add (mul 2 3) (mul 2 3).

Section TestNoSimpl.
Variable x : int.
Eval simpl in add (add 1 2) x.
Eval hnf in add (add 1 2) x.
End TestNoSimpl.
