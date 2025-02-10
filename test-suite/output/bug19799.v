Require Import ZArith_base Zcomplements. Local Open Scope Z_scope.

(* Set Typeclasses Debug Verbosity 1. *)
Goal forall A acc,  Zlength_aux acc A nil = acc + Z.of_nat (@length A nil).
Proof.
  Succeed (solve [info_auto with zarith]).
  Succeed (solve [info_eauto with zarith]).
  Fail (solve [typeclasses eauto with zarith core]).
    (* no applicable tactic *)
Abort.
