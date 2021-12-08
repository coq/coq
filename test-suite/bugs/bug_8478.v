Set Universe Polymorphism.
Set Printing Universes.
Unset Strict Universe Declaration.

Monomorphic Universe v.

Section Foo.
  Let bar := Type@{u}.
  Fail Monomorphic Constraint bar.u < v.

End Foo. (* was anomaly undeclared universe due to the constraint *)
