Require Import TestSuite.admit.
Module JGross.
  Hint Extern 1 => match goal with |- match ?E with end => case E end.

  Goal forall H : False, match H return Set with end.
  Proof.
    intros.
    solve [ eauto ].
  Qed.
End JGross.

Section BenDelaware.
  Hint Extern 0 => admit.
  Goal forall (H : False), id (match H return Set with end).
  Proof.
    eauto.
  Qed.
  Goal forall (H : False), match H return Set with end.
  Proof.
    solve [ eauto ] .
  Qed.
End BenDelaware.
