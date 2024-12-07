Polymorphic Inductive eq@{s s'|l +|} {A:Type@{s|l}} (x:A) : A -> Type@{s'|_} :=
  eq_refl : eq x x.

Check eq 0 0 : SProp.
Check eq 0 0 : Prop.
