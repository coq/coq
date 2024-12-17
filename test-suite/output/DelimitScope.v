Reserved Notation "~~ b" (at level 35, right associativity).

Notation "~~ b" := (negb b) : bool_scope.

Check negb false.

Delimit Scope bool_scope with B.

Check negb false.

(* %bool still works even if not used by printing *)
Check (~~ false)%bool.
Check (~~ false)%B.
