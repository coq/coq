(* -*- coq-prog-args: ("-async-proofs" "no"); -*- *)
(* disable async proofs because they get the parse error before running the Fail *)

Fail Timeout 0 Check True.

(* parse error *)
Timeout -1 Check True.
