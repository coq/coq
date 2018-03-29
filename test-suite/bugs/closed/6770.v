Section visibility.

  Let Fixpoint by_proof (n:nat) : True.
  Proof. exact I. Defined.
End visibility.

Fail Check by_proof.
