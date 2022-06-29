
Class Bar := {}.
#[export] Instance bb : Bar := {}.

Class Foo := { xx : Bar; foo : nat }.

Fail #[export] Instance bar : Foo := { foo := 1 + 1; foo := 2 + 2 }.
