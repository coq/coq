Set Universe Polymorphism.
Set Printing Universes.

Axiom foo@{i j} : Type@{i} -> Type@{j}.

Notation bar := foo.

Monomorphic Universes i j.

Check bar@{i j}.
Fail Check bar@{i}.

Notation qux := (nat -> nat).

Fail Check qux@{i}.

Axiom TruncType@{i} : nat -> Type@{i}.

Notation "n -Type" := (TruncType n) (at level 1) : type_scope.
Notation hProp := (0)-Type.

Check hProp.
Check hProp@{i}.

