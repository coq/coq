Goal True.
Proof.
  assert nat;clear.
  refine ?[foo].
  [foo]:shelve.
  exact I.

  [foo]: refine (_ + _).

  Unshelve.
  1,2: exact 0.
Qed.
