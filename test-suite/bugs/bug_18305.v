#[global] Remove Hints plus_n_O : core.

Goal forall n, n = n + 0.
Proof.
intros.
Fail now trivial.
Abort.
