(* Various meaningless notations *)
Notation "1" := 0 (at level 3).
Fail Notation "#" := 0 (only parsing, only parsing).
Fail Notation "#" := 0 (only parsing, only printing).
Fail Notation "#" := 0 (only printing, only printing).
Notation "#" := 0 (only parsing, format "#").
