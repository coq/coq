Ltac int1 := let h := fresh in intro h.

Goal nat -> nat -> True.
  let h' := fresh in (let h := fresh in intro h); intro h'.
  Restart. let h' := fresh in int1; intro h'.
  trivial.
Qed.


