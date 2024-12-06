(* @eladrion's example for issue #18212 *)

From Corelib Require Extraction.

(* Define an axiomatic function. *)
Axiom ax_fun : nat -> nat.

(* Define a fully specified function*)
Definition exact_fun (a : nat) := (ax_fun a) + 1.

(* Define duplicate of the fully specified function*)
Definition exact_fun2 (a : nat) := (ax_fun a) + 1.

(* before we give the directive axioms produce failwith "axiom to be realized" *)
Extraction ax_fun.

(* ax_fun shall be a FFI call to the C function my_c_fun *)
Extract Foreign Constant ax_fun => "my_c_fun".
Extraction ax_fun.

(* Extract exact_fun *)
Extraction exact_fun.

(* exact_fun shall now be a FFI call to the C function my_c_fun *)
Extract Foreign Constant exact_fun => "my_exact_c_fun".
Extraction exact_fun.

(* Now, exact_fun is an entry point exposed to C *)
Extract Callback "call_exact_fun" exact_fun2.
Extraction exact_fun2.

(* Now we make sure that a callback registration can be reverted *)
Reset Extraction Callback.
Extraction exact_fun2.
