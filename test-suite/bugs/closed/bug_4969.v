Require Import Classes.Init.

Class C A := c : A.
Instance nat_C : C nat := 0.
Instance bool_C : C bool := true.
Lemma silly {A} `{C A} : 0 = 0 -> c = c -> True.
Proof. auto. Qed.

Goal True.
  class_apply @silly; [reflexivity|].
  reflexivity. Fail Qed.
