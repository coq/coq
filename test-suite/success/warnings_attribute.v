
Set Primitive Projections.

Fail #[warnings="+non-primitive-record"]
 Record foo : Prop := { _ : nat }.

#[warnings="-non-primitive-record"]
 Record foo : Prop := { _ : nat }.
