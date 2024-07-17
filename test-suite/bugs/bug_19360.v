Module M. Axiom x : nat. End M.

Module UnfilteredWithSection.
  Module N.
    Section S. Export M. End S.
    Check x.
  End N.

  Import N.
  Check x.
End UnfilteredWithSection.

Module NameOnlyWithSection.
  Module N'.
    Section S. Export M(x). End S.
    Check x.
  End N'.
  Fail Check x.

  Import N'.
  Check x.
End NameOnlyWithSection.
