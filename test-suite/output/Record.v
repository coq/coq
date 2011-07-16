Record test := build { field : nat }.
Record test_r := build_r { field_r : nat }.
Record test_c := build_c { field_c : nat }.

Add Printing Constructor test_c.
Add Printing Record test_r.

Set Printing Records.

Check build 5.
Check {| field := 5 |}.

Check build_r 5.
Check build_c 5.

Unset Printing Records.

Check build 5.
Check {| field := 5 |}.
Check build_r 5.
Check build_c 5.
