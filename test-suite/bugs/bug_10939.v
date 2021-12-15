Goal False.
Proof.
  epose proof ltac:(shelve). (* works *)
  epose proof ltac:(admit). (* anomaly *)
Abort.
