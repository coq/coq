
Module Type E. End E.

Module M.
  Lemma x : True.
  Proof. trivial. Qed.
End M.


Module Type T.
  Lemma x : True.
  Proof. trivial. Qed.
End T.

Module F(A:E).
  Lemma x : True.
  Proof. trivial. Qed.
End F.
