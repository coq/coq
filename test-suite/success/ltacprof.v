(** Some LtacProf tests *)

Start Profiling.
Ltac multi := (idtac + idtac).
Goal True.
  try (multi; fail). (* Anomaly: Uncaught exception Failure("hd"). Please report. *)
Admitted.
Show Profile.
