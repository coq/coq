Require Import A.

Definition y := x.

Lemma yeq : y = y.
Proof. pose xeq. auto. Qed.


Section Foo.

Variable (HFalse : False).

Lemma yeq' : y = y.
Proof using HFalse. elimtype False. apply HFalse. Qed.

End Foo.

Module Type E. End E.

Module M.
  Lemma x : True.
  Proof. trivial. Qed.
End M.


Module Type T.
  Lemma x : True.
  Proof. trivial. Qed.
End T.

Module F(X:E).
  Lemma x : True.
  Proof. trivial. Qed.
End F.
