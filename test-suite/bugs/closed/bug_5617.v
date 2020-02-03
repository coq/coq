Set Primitive Projections.
Record T X := { F : X }.

Fixpoint f (n : nat) : nat :=
match n with
| 0 => 0
| S m => F _ {| F := f |} m
end.
