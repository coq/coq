Ltac f := fail.
Ltac inj := injection.

Goal False.
Fail idtac; easy.
Fail idtac; f.
Fail idtac; inj.
Fail let x := fail in x || x.
Abort.
