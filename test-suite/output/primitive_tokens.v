Require Import String.

Record test := { field : nat }.

Open Scope string_scope.

Unset Printing Notations.

Check "foo".
Check 1234.
Check 1 + 2.
Check match "a" with "a" => true | _ => false end.
Check match 1 with 1 => true | _ => false end.
Check {| field := 7 |}.

Set Printing Raw Literals.

Check "foo".
Check 1234.
Check 1 + 2.
Check match "a" with "a" => true | _ => false end.
Check match 1 with 1 => true | _ => false end.
Check {| field := 7 |}.
