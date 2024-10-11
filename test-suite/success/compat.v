(* -*- coq-prog-args: ("-compat-from" "TestSuite" "admit"); -*- *)
(* Check that TestSuite.admit was required *)
Goal False.
Proof. exact TestSuite.admit.proof_admitted. Qed.
(* and also imported *)
Goal False.
Proof. exact proof_admitted. Qed.
