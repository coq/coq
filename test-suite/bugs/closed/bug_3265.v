Require Import Setoid.
Hint Extern 0 => apply reflexivity : typeclass_instances.
Goal forall (B : Type) (P : B -> Prop), exists y : B, P y.
  intros.
  try reflexivity. (* Anomaly: Uncaught exception Not_found. Please report. *)
Abort.
