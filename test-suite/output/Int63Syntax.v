Require Import Int63 Cyclic63.

Check 2%int63.
Check (2 + 2)%int63.
Open Scope int63_scope.
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
Check (Int63.add 2 2).
Check (2+2).
Eval vm_compute in 2+2.
Eval vm_compute in 65675757 * 565675998.
Fail Check -1.
Fail Check 9223372036854775808.
Open Scope nat_scope.
Check 2. (* : nat *)
Check 2%int63.
Delimit Scope int63_scope with i63.
Definition t := 2%int63.
Print t.
Delimit Scope nat_scope with int63.
Print t.
Check 2.
Close Scope nat_scope.
Check 2.
Close Scope int63_scope.
