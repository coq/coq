Record t := {x : bool; y : bool; z : bool}.

Goal forall x1 x2 y z,
  {| x := x1; y := y; z := z |} = {| x := x2; y := y; z := z |} -> x1 = x2.
Proof.
intros; congruence. (* was doing stack overflow *)
Qed.
