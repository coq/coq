Ltac foo tac := tac.

Goal True.
Proof.
foo subst.
Admitted.
