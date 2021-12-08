Set Universe Polymorphism.
Definition foo : True.
  abstract exact I.
Defined.
Eval hnf in foo. (* Should not be [I] *)
Goal True.
Proof.
  Fail unify foo I.
Abort.
