(* Various meaningless notations *)
Fail Notation "#" := 0 (only parsing, only parsing).
Fail Notation "#" := 0 (only parsing, only printing).
Fail Notation "#" := 0 (only printing, only printing).
Notation "#" := 0 (only parsing, format "#").

(* Alerting about primitive syntax *)
Notation "1" := tt (at level 3).
Check 1%nat.
Fail Reserved Notation "1".

Notation """tt""" := tt (at level 2).
Check "tt".
From Stdlib Require Import String.
Check "tt"%string.
Fail Reserved Notation """tt""".

(* Test string literals themselves with double quotes *)
Notation """t""""t""" := tt.
Check "t""t".

Module A.

(* Not forced to be a keyword *)
Notation "# ""|"" a" := (Some a) (at level 0, a at level 0).
Check # "|" true.
Check "|"%string.

(* Now forced to be a keyword *)
Notation "a ""|"" b" := (a, b) (at level 50).
Check 2 "|" 4.

End A.

Module B.

Notation " ""I'm true"" " := true.
Check "I'm true".

Notation """""" := false. (* Empty string *)
Check "".

End B.

Module C.

Notation "symbolwith""doublequote" := true (only printing).
Check true.

Notation "'""'" := false (only printing). (* double quote *)
Check false.

End C.
