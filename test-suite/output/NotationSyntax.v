(* Various meaningless notations *)
Fail Notation "#" := 0 (only parsing, only parsing).
Fail Notation "#" := 0 (only parsing, only printing).
Fail Notation "#" := 0 (only printing, only printing).
Notation "#" := 0 (only parsing, format "#").

(* Alerting about primitive syntax *)
Notation "1" := tt (at level 3).
Check 1%nat.
Fail Reserved Notation "1".
