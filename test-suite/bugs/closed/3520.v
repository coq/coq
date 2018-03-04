Set Primitive Projections.

Record foo (A : Type) := 
  { bar : Type ; baz := Set; bad : baz = bar }.

Set Nonrecursive Elimination Schemes.

Record notprim : Prop :=
  { irrel : True; relevant : nat }.



