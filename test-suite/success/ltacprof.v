(** Some LtacProf tests *)

Set Ltac Profiling.
Ltac multi := (idtac + idtac).
Goal True.
  try (multi; fail). (* Used to result in: Anomaly: Uncaught exception Failure("hd"). Please report. *)
Admitted.
Show Ltac Profile.
