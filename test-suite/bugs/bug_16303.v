Fact uip_nat {n : nat} (e : n = n) : e = eq_refl.
(* Should not fail with an anomaly *)
Fail refine match e with eq_refl => eq_refl end.
Abort.
