Goal (n:nat)(n=O)->(n=O).
Intros.
Rename n into p.
NewInduction p; Auto.
Qed.
