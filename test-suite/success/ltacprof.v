(** Some LtacProf tests *)

Set Ltac Profiling.
Ltac multi := (idtac + idtac).
Goal True.
  try (multi; fail). (* Used to result in: Anomaly: Uncaught exception Failure("hd"). Please report. *)
Admitted.
Show Ltac Profile.

(* backtracking across profiler manipulation *)
Unset Ltac Profiling.
Reset Ltac Profile.

Fixpoint slow (n : nat) : unit
  := match n with
     | 0 => tt
     | S n => fst (slow n, slow n)
     end.

Ltac slow := idtac; let v := eval cbv in (slow 16) in idtac.
Ltac multi2 :=
  try (((idtac; slow) + (start ltac profiling; slow) + (idtac; slow) + (slow; stop ltac profiling; slow) + slow + (start ltac profiling; (idtac + slow); ((stop ltac profiling + idtac); fail))); slow; fail); slow; show ltac profile.
Goal True.
  multi2.
Admitted.
