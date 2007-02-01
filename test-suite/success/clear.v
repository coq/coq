Goal forall x:nat, (forall x, x=0 -> True)->True.
  intros; eapply H.
  instantiate (1:=(fun y => _) (S x)).
  simpl.
  clear x || trivial.
Qed.
