Set Printing Universes.
Definition foo : Type.
Proof.
  assert (H : Set) by abstract (assert Type by abstract exact Type using bar; exact nat).
  exact bar.
Defined. (* Toplevel input, characters 0-8:
Error:
The term "(fun _ : Set => bar) foo_subproof" has type
"Type@{Top.2}" while it is expected to have type "Type@{Top.1}". *)
