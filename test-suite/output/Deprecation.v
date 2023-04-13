#[deprecated(since = "X.Y", note = "Use idtac instead.")]
 Ltac foo := idtac.

Goal True.
foo.
Abort.

Set Warnings "-deprecated-since-X.Y".

Goal True.
foo.
Abort.

Set Warnings "+deprecated-since-X.Y".

Goal True.
Fail foo.
Abort.

#[deprecated(since = "library X.Y", note = "Use baz instead.")]
 Ltac bar := idtac.

Goal True.
bar.
Abort.
