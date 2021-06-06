Require Import Uint63 Cyclic63.

Open Scope uint63_scope.

(* This used to go through because of an unbalanced stack bug in the bytecode
interpreter *)

Lemma bad : False.
assert (1 = 2).
change 1 with (Uint63.add (Uint63.addmuldiv 129 (Uint63.add 1 1) 2) 1).
Fail vm_compute; reflexivity.
(*
discriminate.
Qed.
*)
Abort.
