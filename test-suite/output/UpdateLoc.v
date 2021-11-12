Ltac r0 := refine 0.

Goal False.
Proof.
  Fail refine 0. (* before: whole tactic, after: just 0 *)
  Fail r0. (* before: "refine 0" in the ltac definition, after: r0 in this line *)
Abort.
