Tactic Notation "foo" constr60(x) "=" constr60(y) := idtac "foo"; idtac x; idtac y.

Goal False.
Proof.
foo 3 + 1 = 4.
Abort.

Tactic Notation "bar" open_constr60(x) "=" open_constr60(y) := idtac "bar"; idtac x; idtac y.

Goal False.
Proof.
Fail foo 3 + _ = 4.
bar 3 + _ = 4.
Abort.

Tactic Notation "baz" uconstr60(x) "=" uconstr60(y) := idtac "baz"; idtac x; idtac y.

Goal False.
Proof.
Fail foo 3 + x = 4.
Fail bar 3 + x = 4.
baz 3 + x = 4.
Abort.
