Module Foo.
  Record foor := C { eq : Type }.
End Foo.

Module bar.

  Goal forall x : Foo.foor, x = x.
  Proof.
    intro x.
    destruct x.
    revert eq0.
    exact (fun f => eq_refl (Foo.C f)).
  Qed.
End bar.
