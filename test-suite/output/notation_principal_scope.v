Arguments conj {_ _} _ _%_function.

Set Warnings "+inconsistent-scopes".
Fail Notation pp X := (conj X X).

Fail Notation pp := 1 (only printing).

Fail Notation pp X := nonexisting.

Fail Notation pp X := (conj X X) (X, X in scope nat_scope).

Notation pp X := (conj X X) (X in scope nat_scope).

Notation "$" := I (only parsing) : nat_scope.
Notation "$" := (I I) (only parsing) : bool_scope.

Open Scope bool_scope.
Check pp $.
Fail Check pp (id $).

Notation pp1 X := (X%nat) (X in scope bool_scope).
Notation pp2 X := ((X + X)%type) (X in scope bool_scope).
Notation pp3 X := (((X, X)%type, X)%nat) (X in scope bool_scope).
