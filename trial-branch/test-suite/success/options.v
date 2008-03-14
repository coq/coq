(* Check that the syntax for options works *)
Set Implicit Arguments.
Unset Strict Implicit.
Set Strict Implicit.
Unset Implicit Arguments.
Test Implicit Arguments.

Set Printing Coercions.
Unset Printing Coercions.
Test Printing Coercions.

Set Silent.
Unset Silent.
Test Silent.

Set Printing Depth 100.
Test Printing Depth.

Parameter i : bool -> nat.
Coercion i : bool >-> nat.
Add Printing Coercion i.
Remove Printing Coercion i.
Test Printing Coercion for i.

Test Printing Let.
Test Printing If.
Remove Printing Let sig.
Remove Printing If bool.

Unset Printing Synth.
Set Printing Synth.
Test Printing Synth.

Unset Printing Wildcard.
Set Printing Wildcard.
Test Printing Wildcard.
