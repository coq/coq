Tactic Notation "evarr" open_constr(x) := let y := constr:(x) in exact y.

Goal True.
  evarr _.
Admitted.
Goal True.
  Fail exact ltac:(evarr _). (* Error: Cannot infer this placeholder. *)
