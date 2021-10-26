Module Foo.
  Record foor := C { foof : Type }.
End Foo.

Module bar.
  Import Foo.

  Goal forall x : foor, x = x.
  Proof.
    intro x.
    destruct x.
    revert foof.
    exact (fun f => eq_refl (C f)).
  Qed.
End bar.
