(* Check that the syntax for options works *)
Set Implicit Arguments.
Unset Implicit Arguments.
Test Implicit Arguments.

Set Printing Coercions.
Unset Printing Coercions.
Test Printing Coercions.

Set Silent.
Unset Silent.
Test Silent.

Set Printing Depth 100.
Print Table Printing Depth.

Parameter i : bool -> nat.
Coercion i : bool >-> nat.
Set Printing Coercion i.
Unset Printing Coercion i.
Test Printing Coercion i.

Print Table Printing Let.
Print Table Printing If.
Remove Printing Let sig.
Remove Printing If bool.

Unset Printing Synth.
Set Printing Synth.
Test Printing Synth.

Unset Printing Wildcard.
Set Printing Wildcard.
Test Printing Wildcard.
