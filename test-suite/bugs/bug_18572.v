Parameters F G: Prop.

Axiom F2G: F -> G.

Goal F -> exists n: nat, n * n = 0.
Proof.
  intros HF.
  eapply ex_ind.
  intros x Hx.
  unshelve eexists. (* Check that [x] is not cleared *)
  2:clear HF.
  Fail Check HF. (* check that HF is transitively cleared *)
  exact x.
  exact Hx.
  exists 0.
  reflexivity.
Qed.
