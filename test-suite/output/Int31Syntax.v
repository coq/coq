Require Import Int31 Cyclic31.

Open Scope int31_scope.
Check I31. (* Would be nice to have I31 : digits->digits->...->int31
              For the moment, I31 : digits31 int31, which is better
	      than (fix nfun .....) size int31 *)
Check 2.
Check 1000000000000000000. (* = 660865024, after modulo 2^31 *)
Check (add31 2 2).
Check (2+2).
Eval vm_compute in 2+2.
Eval vm_compute in 65675757 * 565675998.
Close Scope int31_scope.
