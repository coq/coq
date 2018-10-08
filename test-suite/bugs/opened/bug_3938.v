Require Import Coq.Arith.PeanoNat.
Hint Extern 1 => admit : typeclass_instances.
Goal forall a b (f : nat -> Set), Nat.eq a b -> f a = f b.
  intros a b f H.
  rewrite H. (* Toplevel input, characters 15-25:
Anomaly: Evar ?X11 was not declared. Please report. *)
