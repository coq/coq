Ltac bar x := refine x.
Goal False -> False.
Proof.
  intro x.
  Fail bar doesnotexist.
Abort.
