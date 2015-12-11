Set Printing Universes.
Definition foo : Type.
Proof.
  assert (H : Set) by abstract (assert Type by abstract exact Type using bar; exact nat).
  exact bar.
Defined. (* Toplevel input, characters 0-8:
Error: