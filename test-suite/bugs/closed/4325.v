Goal (forall a b : nat, Set = (a = b)) -> Set.
Proof.
  clear.
  intro H.
  erewrite (fun H' => H _ H').
