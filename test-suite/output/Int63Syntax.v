Require Import Int63 Cyclic63.

Open Scope int63_scope.
Check 2.
Check 9223372036854775807.
Check (Int63.add 2 2).
Check (2+2).
Eval vm_compute in 2+2.
Eval vm_compute in 65675757 * 565675998.
Fail Check -1.
Fail Check 9223372036854775808.
Close Scope int63_scope.
