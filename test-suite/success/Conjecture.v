(* Check keywords Conjecture and Admitted are recognized *)

Conjecture c : (n:nat)n=O.

Check c.

Theorem d : (n:nat)n=O.
Proof.
  NewInduction n.
  Reflexivity.
  Assert H:False.
  2:NewDestruct H.
Admitted.
