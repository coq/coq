Primitive Blocked := #blocked_type.

Primitive block : forall (T : Type), T -> Blocked T := #block.
Primitive unblock : forall (T : Type), Blocked T -> T := #unblock.

Primitive run : forall (T K : Type), Blocked T -> (T -> K) -> K := #run.

Arguments block {_} _.
Arguments unblock {_} _.
Arguments run {_ _} _ _.
