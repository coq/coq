Module Import foo.
Module Import bar.
  Definition x := I.
End bar.
Notation y := (ltac:(exact x)) (only parsing).
End foo.

Check y.
(* Error: The reference x was not found in the current environment. *)

Axiom x : True.
Check eq_refl : y = bar.x.
