(* An example where it does not hurt having more type-classes resolution *)
Class some_type := { Ty : Type }.
Instance: some_type := { Ty := nat }.
Arguments Ty : clear implicits.
Goal forall (H : forall t : some_type, @Ty t -> False) (H' : False -> 1 = 2), 1 = 2.
Proof.
intros H H'.
specialize (H' (@H _ O)). (* was failing *)
