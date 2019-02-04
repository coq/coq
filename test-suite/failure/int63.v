Require Import Int63 Cyclic63.

Open Scope int63_scope.

(* This used to go through because of an unbalanced stack bug in the bytecode
interpreter *)

Lemma bad : False.
assert (1 = 2).
change 1 with (Int63.add (Int63.addmuldiv 129 (Int63.add 1 1) 2) 1).
Fail vm_compute; reflexivity.
(*
discriminate.
Qed.
*)
Abort.
