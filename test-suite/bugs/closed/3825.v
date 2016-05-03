Set Universe Polymorphism.
Set Printing Universes.

Axiom foo@{i j} : Type@{i} -> Type@{j}.

Notation bar := foo.

Monomorphic Universes i j.

Check bar@{i j}.
Fail Check bar@{i}.

Notation qux := (nat -> nat).

Fail Check qux@{i}.

