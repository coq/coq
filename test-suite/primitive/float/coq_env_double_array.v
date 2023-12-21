Require Import PrimFloat.

Goal True.
pose (f := one).
pose (f' := (-f)%float).

(* this used to segfault when the coq_env array given to the
   coq_interprete C function was an unboxed OCaml Double_array
   (created by Array.map in csymtable.ml just before calling
   eval_tcode) *)
vm_compute in f'.

Abort.
