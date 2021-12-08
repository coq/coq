(* This should be an error, not an anomaly *)
Fail Definition foo := fix foo (n : nat) { wf n n } := 0.
