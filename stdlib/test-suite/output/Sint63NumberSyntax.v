From Stdlib Require Import Sint63.

Check 2%sint63.
Open Scope sint63_scope.
Check 2.
Check -3.
Check 4611686018427387903.
Check -4611686018427387904.
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
Fail Check 4611686018427387904.
Fail Check -4611686018427387905.

Set Printing All.
Check 1%sint63.
Check (-1)%sint63.
Unset Printing All.

Open Scope nat_scope.
Check 2. (* : nat *)
Check 2%sint63.
Delimit Scope sint63_scope with si63.
Definition t := 2%sint63.
Print t.
Delimit Scope nat_scope with sint63.
Print t.
Check 2.
Close Scope nat_scope.
Check 2.
Close Scope sint63_scope.
Delimit Scope sint63_scope with sint63.

Check (2 + 2)%sint63.
Open Scope sint63_scope.
Check (2+2).
Eval vm_compute in 2+2.
Eval vm_compute in 65675757 * 565675998.
