Require Import Classes.Init.

Class C A := c : A.
#[export] Instance nat_C : C nat := 0.
#[export] Instance bool_C : C bool := true.
Lemma silly {A} `{C A} : 0 = 0 -> c = c -> True.
Proof. auto. Qed.

Goal True.
  class_apply @silly; [reflexivity|].
  reflexivity. Fail Qed.
Abort.
