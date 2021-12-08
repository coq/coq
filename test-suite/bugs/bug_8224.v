(* Checking that terms are evar-free before being grounded *)

(* This used to raise an anomaly in 8.9 beta *)

Fail Fixpoint restrict f n :=
  match n with
  | O => nil
  | S n => cons (f n) (restrict f n)
  end.
