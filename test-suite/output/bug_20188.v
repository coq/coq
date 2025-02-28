Require Import Ltac2.Ltac2.
Notation "[[ x ]]" := ltac2:(()) (only parsing).
Notation "[ x ]" := ltac2:(let x := Ltac2.Constr.pretype x in exact $x) (only parsing).
Fail Check foo. (* Error: The reference foo was not found in the current environment. *)
Check [[ foo ]]. (* success *)
Check [ foo ].
