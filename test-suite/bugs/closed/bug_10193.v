Section test.
  Variable V : Type.
  Variable zeroV : V.
  Notation "0V" := zeroV.
  Locate "0V". (* Notation "0V" := zeroV (default interpretation) *)
  Check 0V.
End test.
