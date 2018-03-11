(* these should succeed, no warning printed *)

Set Printing All.
Set Printing Sugared.
Set Printing Defaults.

Set Printing All.
Test Printing Implicit. (* on *)

Unset Printing All.
Test Printing Implicit. (* off *)

Unset Printing All. (* warning *)
