
Module E. End E.
Module Type ET. End ET.

Section S.
  Fail Module Type Prover.

  Fail Module M.

  Fail Module M := E.

  Fail Module Type M := ET.

  Fail Include E.

  Fail Declare Module M : ET.
End S.
