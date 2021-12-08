Arguments ex_intro [A].

Goal exists n : nat, True.
  eapply ex_intro. exact 0. exact I.
Qed.
