Goal exists n, n = 0.
  eexists ?[n].
  progress (unify ?n 0).
Abort.

Goal exists n, n = 0 -> True.
  eexists ?[n].
  intros.
  progress (unify ?n 0).
(* Toplevel input, characters 0-22: *)
(* > progress (unify ?n 0). *)
(* > ^^^^^^^^^^^^^^^^^^^^^^ *)
(* Error: Failed to progress. *)
Abort.
