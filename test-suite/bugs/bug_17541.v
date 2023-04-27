(* Check that the case tactic does not reduce on constructors *)
Goal True.
Proof.
case 0.
+ exact I.
+ match goal with [ |- nat -> True ] => idtac end.
  intro; exact I.
Qed.
