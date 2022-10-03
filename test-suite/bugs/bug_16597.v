Goal exists A, forall (H : forall b : A, b = b), True.
eexists. intro.
try congruence. (* Used to fail with Anomaly "in econstr: grounding a non evar-free term" *)
Abort.
