(* -*- coq-prog-args: ("-bytecode-compiler" "no"); -*- *)

Eval lazy in 0.
Eval vm_compute in 0.

Set Warnings "+vm-compute-disabled".
Fail Eval vm_compute in 0.
