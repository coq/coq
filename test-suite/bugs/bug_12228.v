Tactic Notation "mark" constr(P) "at" integer_list(L) := pattern P at L.
Goal 0 = 0.
mark 0 at -2.
Abort.
