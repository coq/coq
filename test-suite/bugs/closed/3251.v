Goal True.
Ltac foo := idtac.
(* print out happens twice:
foo is defined
foo is defined

... that's fishy.  But E. Tassi tells me that it's correct, because it happens on two threads. *)
Undo.
Ltac foo := idtac.
(* Before 5b39c3535f7b3383d89d7b844537244a4e7c0eca, this would print out: *)
(* Anomaly: Backtrack.backto to a state with no vcs_backup. Please report. *)
