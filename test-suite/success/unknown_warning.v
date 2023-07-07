Set Warnings "+unknown-warning".

Set Warnings "-foo".
Fail Set Warnings "foo".
Fail Set Warnings "+foo".

#[warnings="-foo"] Check True.
Fail #[warnings="foo"] Check True.

(* debatable: even though "all" overrides "+foo" we still warn *)
Fail Set Warnings "+foo,-all".

(* debatable: changing unknown-warning has no effect for the current check *)
Fail Set Warnings "-unknown-warning,foo".
Fail #[warnings="-unknown-warning,foo"] Check True.
Set Warnings "-unknown-warning".
#[warnings="+unknown-warning,foo"] Check True.
