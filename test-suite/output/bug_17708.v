Notation zero := (ltac: (exact 0)).
Ltac foo := exact zero.
Print foo.
