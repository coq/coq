Require Import Int31 Cyclic31.

Open Scope int31_scope.

(* This used to go through because of an unbalanced stack bug in the bytecode
interpreter *)

Lemma bad : False.
assert (1 = 2).
change 1 with (add31 (addmuldiv31 65 (add31 1 1) 2) 1).
Fail vm_compute; reflexivity.
(*
discriminate.
Qed.
*)
Abort.

