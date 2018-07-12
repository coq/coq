Set Warnings "+deprecated".

#[deprecated(since = "8.8", note = "Use idtac instead")]
Ltac foo x := idtac.

Goal True.
Fail (foo true).
Abort.

Fail Ltac bar := foo.
Fail Tactic Notation "bar" := foo.

#[deprecated(since = "8.8", note = "Use idtac instead")]
Tactic Notation "bar" := idtac.

Goal True.
Fail bar.
Abort.

Fail Ltac zar := bar.

Set Warnings "-deprecated".

Ltac zar := foo.
Ltac zarzar := bar.

Set Warnings "+deprecated".

Goal True.
zar x.
zarzar.
Abort.
