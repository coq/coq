Require Import Setoid.
Goal forall x y : Type, x = y -> x = y.
intros x y H.
Fail setoid_rewrite H.
(* Toplevel input, characters 0-16:
Anomaly: Uncaught exception Reduction.NotConvertible(_). Please report. *)
