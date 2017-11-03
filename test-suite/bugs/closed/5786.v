(* Printing all kinds of Ltac generic arguments *)

Tactic Notation "myidtac" string(v) := idtac v.
Goal True.
myidtac "foo".
Abort.

Tactic Notation "myidtac2" ref(c) := idtac c.
Goal True.
myidtac2 True.
Abort.

Tactic Notation "myidtac3" preident(s) := idtac s.
Goal True.
myidtac3 foo.
Abort.

Tactic Notation "myidtac4" int_or_var(n) := idtac n.
Goal True.
myidtac4 3.
Abort.

Tactic Notation "myidtac5" ident(id) := idtac id.
Goal True.
myidtac5 foo.
Abort.



