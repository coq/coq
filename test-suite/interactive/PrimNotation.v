(* Until recently, the Notation.declare_numeral_notation wasn't synchronized
   w.r.t. backtracking. This should be ok now.
   This test is pretty artificial (we must declare Z_scope for this to work).
*)

Delimit Scope Z_scope with Z.
Open Scope Z_scope.
Check 0.
(* 0 : nat *)
Require BinInt.
Check 0.
(* 0 : BinNums.Z *)
Back 2.
Check 0.
(* Expected answer: 0 : nat *)
(* Used to fail with:
Error: Cannot interpret in Z_scope without requiring first module BinNums.
*)
