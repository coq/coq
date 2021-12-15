Global Generalizable All Variables.

Section test.
  Context {A : Type}.
  Context `{!foo A}.

  Goal foo A.
  Proof. assumption. Defined.
End test.
