(* Test Conjecture/Admitted *)

Conjecture c : (n:nat)n=O.
Proof.
  NewInduction n.
  Reflexivity.
  Assert H:False.
  2:NewDestruct H.
Admitted.
