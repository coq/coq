(* -*- coq-prog-args: ("-bytecode-compiler" "no"); -*- *)

(* Ordinary [vm_compute] has a supported [compute] fallback in this mode. *)
Eval vm_compute in 0.

(* Regression probes: the two new vm_compute variants should have an explicit,
   compatible fallback policy rather than bypassing the existing wrapper. *)
Eval vm_compute_no_stuck in 0.
Eval vm_compute_whnf in 0.
