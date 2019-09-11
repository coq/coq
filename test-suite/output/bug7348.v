Require Extraction.

Extraction Language OCaml.
Set Extraction KeepSingleton.

Module Case1.

Record rec (x : bool) := { f : bool }.

Definition silly x (b : rec x) :=
  if x return (if x then bool else unit) then f x b else tt.

End Case1.

Module Case2.

Record rec (x : bool) := { f : bool -> bool }.

Definition silly x (b : rec x) :=
  if x return (if x then bool else unit) then f x b false else tt.

End Case2.

Extraction TestCompile Case1.silly Case2.silly.
Recursive Extraction Case1.silly Case2.silly.
