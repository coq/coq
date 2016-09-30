Axiom silly : 1 = 1 -> nat -> nat.
Goal forall pf : 1 = 1, silly pf 0 = 0 -> True.
  Fail generalize (@eq nat).
