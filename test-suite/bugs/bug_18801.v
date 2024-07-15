(* -*- coq-prog-args: ("-allow-rewrite-rules"); -*- *)

Symbol dom : Prop -> Prop.
Rewrite Rule dom_rew := dom (forall (x : ?A), ?B) => ?A.

Eval cbv in dom (True -> True).
