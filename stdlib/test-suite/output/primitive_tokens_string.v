From Stdlib Require Import String.

Open Scope string_scope.

Unset Printing Notations.

Check "foo".
Check match "a" with "a" => true | _ => false end.

Set Printing Raw Literals.

Check "foo".
Check match "a" with "a" => true | _ => false end.
