Set Primitive Projections.

Module M.

CoInductive foo := Foo {
  foo0 : foo;
  foo1 : bar;
}
with bar := Bar {
  bar0 : foo;
  bar1 : bar;
}.

CoFixpoint f : foo := Foo f g
with g : bar := Bar f g.

Check (@eq_refl _ g.(bar0) <: f.(foo0).(foo0) = g.(bar0)).
Check (@eq_refl _ g <: g.(bar1).(bar0).(foo1) = g).

End M.

Module N.

Inductive foo := Foo {
  foo0 : option foo;
  foo1 : list bar;
}
with bar := Bar {
  bar0 : option bar;
  bar1 : list foo;
}.

Definition f_0 := Foo None nil.
Definition g_0 := Bar None nil.

Definition f := Foo (Some f_0) (cons g_0 nil).

Check (@eq_refl _ f.(foo1) <: f.(foo1) = cons g_0 nil).

End N.
