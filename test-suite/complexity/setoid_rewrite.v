(* Check bug #1176 *)
(* Expected time < 0.50s *)

Require Import Setoid.

Variable f : nat -> Prop.

Goal forall U:Prop, f 100 <-> U.
intros U.
Timeout 5 Time setoid_replace U with False.
