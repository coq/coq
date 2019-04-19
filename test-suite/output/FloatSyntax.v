Require Import Floats.

Check 2%float.
Check 2.5%float.
Check (-2.5)%float.
(* Avoid exponents with less than three digits as they are usually
   displayed with two digits (1e7 is displayed 1e+07) except on
   Windows where three digits are used (1e+007). *)
Check 2.5e123%float.
Check (-2.5e-123)%float.
Check (2 + 2)%float.
Check (2.5 + 2.5)%float.

Open Scope float_scope.

Check 2.
Check 2.5.
Check (-2.5).
Check 2.5e123.
Check (-2.5e-123).
Check (2 + 2).
Check (2.5 + 2.5).

Open Scope nat_scope.

Check 2.
Check 2%float.

Delimit Scope float_scope with flt.
Definition t := 2%float.
Print t.
Delimit Scope nat_scope with float.
Print t.
Check 2.
Close Scope nat_scope.
Check 2.
Close Scope float_scope.
