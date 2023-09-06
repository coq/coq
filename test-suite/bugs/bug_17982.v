
Set Warnings "+notation-overridden".

Fail Infix "+" := Nat.mul : nat_scope.

#[warnings="-notation-overridden"] Infix "+" := Nat.mul : nat_scope.
(* Warning: This command does not support this attribute: warnings.
[unsupported-attributes,parsing,default] *)
