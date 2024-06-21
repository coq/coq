#[universes(polymorphic)]
Inductive t@{u} : Prop := mkt : t.

Inductive runner_sum A := success (a : A).
(* This inductive should not be template polymorphic as u is not substitutable by an algebraic *)
Inductive sum_runner@{u} (A : Type@{u}) (f : t@{u}) := sum_eval : runner_sum A -> sum_runner A f.
