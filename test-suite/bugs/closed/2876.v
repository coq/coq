Lemma test_bug : forall (R:nat->nat->Prop) n m m' (P: Prop),
  P ->
  (P -> R n m) ->
  (P -> R n m') ->
  (forall u, R n u -> u = u -> True) -> 
  True.
Proof.
  intros * HP H1 H2 H3. eapply H3. 
  eauto. (* H1 is used, but H2 should be used since it is the last hypothesis *)
  auto.
Qed.
