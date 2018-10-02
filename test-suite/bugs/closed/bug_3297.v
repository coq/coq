Goal forall (n : nat) (H := eq_refl : n = n) (H' : n = 0), H = eq_refl.
  intros.
  subst. (* Toplevel input, characters 15-20:
Error: Abstracting over the term "n" leads to a term
"λ n : nat, H = eq_refl" which is ill-typed. *)
  Undo.
  revert H.
  subst. (* success *)
  Undo.
  intro.
  clearbody H.
  subst. (* success *)
