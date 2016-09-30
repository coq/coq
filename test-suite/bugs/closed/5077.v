(* Testing robustness of typing for a fixpoint with evars in its type *)

Inductive foo (n : nat) : Type := .
Definition foo_denote {n} (x : foo n) : Type := match x with end.

Definition baz : forall n (x : foo n), foo_denote x.
refine (fix go n (x : foo n) : foo_denote x := _).
Abort.  
