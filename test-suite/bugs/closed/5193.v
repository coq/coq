Class Eqdec A := eqdec : forall a b : A, {a=b}+{a<>b}.

Typeclasses eauto := debug.
Set Typeclasses Debug Verbosity 2.

Inductive Finx(n : nat) : Set :=
| Fx1(i : nat)(e : n = S i)
| FxS(i : nat)(f : Finx i)(e : n = S i).

Context `{Finx_eqdec : forall n, Eqdec (Finx n)}.

Goal {x : Type & Eqdec x}.
  eexists.
  try typeclasses eauto 1 with typeclass_instances.
