Notation bar := ltac:(exact I).
Notation foo := bar (only parsing).
Class baz := { x : False }.
Instance: baz.
Admitted.
Definition baz0 := ((_ : baz) = (_ : baz)).
Definition foo1 := (foo = foo).
Definition baz1 := prod ((_ : baz) = (_ : baz)) (foo = foo).
