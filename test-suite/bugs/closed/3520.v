Set Primitive Projections.

Record foo (A : Type) := 
  { bar : Type ; baz := Set; bad : baz = bar }.

Set Record Elimination Schemes.

Record notprim : Prop :=
  { irrel : True; relevant : nat }.



