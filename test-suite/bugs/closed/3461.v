Lemma foo (b : bool) :
  exists x : nat, x = x.
Proof.
eexists. 
Fail eexact (eq_refl b).
