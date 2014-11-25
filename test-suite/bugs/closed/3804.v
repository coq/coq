Set Universe Polymorphism.
Module Foo.
  Definition T : sigT (fun x => x).
  Proof.
    exists Set.
    abstract exact nat.
  Defined.
End Foo.
Module Bar.
  Include Foo.
End Bar.
Definition foo := eq_refl : Foo.T = Bar.T.
