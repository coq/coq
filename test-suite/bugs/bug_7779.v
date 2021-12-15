(* Checking that the "in" clause takes the "eqn" clause into account *)

Definition test (x: nat): {y: nat | False }. Admitted.

Parameter x: nat.
Parameter z: nat.

Goal
  proj1_sig (test x) = z ->
  False.
Proof.
  intro H.
  destruct (test x) eqn:Heqs in H.
  change (test x = exist (fun _ : nat => False) x0 f) in Heqs. (* Check it has the expected statement *)
Abort.
