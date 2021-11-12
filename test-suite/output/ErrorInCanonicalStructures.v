Record Foo := MkFoo { field1 : nat; field2 : nat -> nat }.

Definition bar := 99.

Fail Canonical Structure Foo.

Fail Canonical Structure bar.
