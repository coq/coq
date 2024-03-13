(* -*- coqchk-prog-args: ("-bytecode-compiler" "yes") -*- *)

Definition foo := 1.

Definition bar := eq_refl 1 <: foo = 1.
