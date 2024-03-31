Definition bar := 0.

Section S.
Let bar := bar.
Definition foo := 0.
Let foo := foo.
End S.

Section S'.
Let bar : nat. exact 0. Defined.
Definition foo' := 0.
Let foo' : nat. exact 0. Defined.
End S'.
