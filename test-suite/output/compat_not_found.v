(* -*- coq-prog-args: ("-compat-from" "Tata" "tutu"); -*- *)
(* From Tata Require tutu. would fail but -compat-from only issues a warning
   and the file compiles fine. *)
Goal True.
Proof. exact I. Qed.
