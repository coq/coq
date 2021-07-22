Unset Primitive Projections.

Record Foo0 := {
  bar0 : Type ;
}.

About Foo0.

#[projections(primitive)]
Record Foo1 := {
  bar1 : Type ;
}.

About Foo1.

#[projections(primitive=yes)]
Record Foo2 := {
  bar2 : Type ;
}.

About Foo2.

#[projections(primitive=no)]
Record Foo3 := {
  bar3 : Type ;
}.

About Foo3.

Set Primitive Projections.

Record Foo4 := {
  bar4 : Type ;
}.

About Foo4.

#[projections(primitive)]
Record Foo5 := {
  bar5 : Type ;
}.

About Foo5.

#[projections(primitive=yes)]
Record Foo6 := {
  bar6 : Type ;
}.

About Foo6.

#[projections(primitive=no)]
Record Foo7 := {
  bar7 : Type ;
}.

About Foo7.
