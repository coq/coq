Goal nat * bool.
Proof.
  split.
  Fail par: exact false.
  Fail par: exact 0.
Abort.
