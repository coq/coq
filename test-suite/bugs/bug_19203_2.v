Set Universe Polymorphism.

Inductive eq@{s s'|u|} {A:Type@{s|u}} (a:A) : A -> Type@{s'|Set} := refl : eq a a.

Register eq as core.eq.type.
Register refl as core.eq.refl.

Goal True.
  remember 0 as x.
  let _ := constr:(Heqx : _ : SProp) in idtac.
  exact I.
Qed.
