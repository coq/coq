Record a_struct := { anum : nat }.
Canonical Structure a_struct_0 := {| anum := 0|}.
Definition rename_a_s_0 := a_struct_0.
Coercion some_nat := (@Some nat).
Definition rename_some_nat := some_nat.
