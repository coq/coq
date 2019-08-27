Require Import Int63 Cyclic63.

Check 2%int63.
Check (2 + 2)%int63.
Open Scope int63_scope.
Check 2.
Check 9223372036854775807.
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
Print Term t.
Delimit Scope nat_scope with int63.
Print Term t.
Check 2.
Close Scope nat_scope.
Check 2.
Close Scope int63_scope.
