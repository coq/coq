Record foo := mkfoo { type : Type }.

Canonical Structure fooA (T : Type) := mkfoo (T -> T).

Definition id (t : foo) (x : type t) := x.

Definition bar := id _ ((fun x : nat => x) : _).
