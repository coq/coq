Require Import Coq.Reals.Reals Coq.nsatz.Nsatz.

Local Open Scope R.

Goal forall a b y1 x2, y1^2 = x2^3 + a * x2 + b -> y1^2 = x2^3 + a * x2 + b -> b = y1^2 - (x2^3 + a * x2).
Proof.
  intros ???? H' ?.
  solve [ rewrite H'; nsatz ] || fail 0 "too early".
  Undo.
  Fail solve [ nsatz ].
Abort. (* change to Qed and remove the above [Fail] when this test passes *)
