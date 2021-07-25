Goal False.
Proof.
  evar (e : Prop). assert e.
  { subst e. Timeout 1 Fail congruence. admit. }
Abort.

Goal False -> False.
Proof.
  evar (e : Prop). assert (H : e -> e).
  { subst e. Timeout 1 congruence. }
  exact H.
Qed.
