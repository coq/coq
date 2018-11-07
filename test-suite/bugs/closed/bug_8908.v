Record foo : Type :=
  { fooA : Type; fooB : Type }.
Definition id {A : Type} (a : A) := a.
Definition untypable : Type.
  unshelve refine (let X := _ in let Y : _ := ltac:(let ty := type of X in exact ty) in id Y).
  exact foo.
  constructor. exact unit. exact unit.
Defined.
