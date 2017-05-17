(* -*- coq-prog-args: ("-time") -*- *)
Definition foo : True.
Proof.
Abort. (* Toplevel input, characters 15-21:
Anomaly: Backtrack.backto to a state with no vcs_backup. Please report. *)
(* Anomaly: VernacAbort not handled by Stm. Please report. *)
