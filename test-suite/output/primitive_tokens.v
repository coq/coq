Record test := { field : nat }.

Unset Printing Notations.

Check 1234.
Check 1 + 2.
Check match 1 with 1 => true | _ => false end.
Check {| field := 7 |}.

Set Printing Raw Literals.

Check 1234.
Check 1 + 2.
Check match 1 with 1 => true | _ => false end.
Check {| field := 7 |}.
