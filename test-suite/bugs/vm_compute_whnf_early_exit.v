(* Regression probe: this term is already constructor-headed.  A weak-head
   variant must not read back the catastrophically large normal form of the
   constructor argument. *)
Axiom n : nat.
Definition explosive := Nat.pow (100 + n) 10.

Timeout 1 Eval vm_compute_whnf in Some explosive.
