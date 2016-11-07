(* Set Printing Existential Instances. *)
Unset Solve Unification Constraints.
Axiom veeryyyyyyyyyyyyloooooooooooooonggidentifier : nat.
Goal True /\ True /\ True \/
             veeryyyyyyyyyyyyloooooooooooooonggidentifier =
             veeryyyyyyyyyyyyloooooooooooooonggidentifier.
  refine (nat_rect _ _ _ _).
  Show.
Admitted.

Set Printing Existential Instances.
Goal forall n m : nat, True /\ True /\ True \/
                        veeryyyyyyyyyyyyloooooooooooooonggidentifier =
                        veeryyyyyyyyyyyyloooooooooooooonggidentifier.
  intros.
  refine (nat_rect _ _ _ _).
  Show.
  clear n. 
  Show.
  3:clear m.
  Show.
Admitted.
