(* Test propagation of clear/clearbody in existential variables *)

Section Test.

Variable p:nat.
Let q := S p.

Goal forall n m:nat, n = m.
intros.
eapply eq_trans.
clearbody q.
clear p. (* Error ... *)

Show Existentials.
