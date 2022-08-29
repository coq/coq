(* Check that an anomaly is not raised *)
Goal exists x, x.
Proof.
simple refine (ex_intro _ _ _).
shelve.
(* The failure is due to Type(u)<=Prop for u an arbitrary sort
   variable being rejected *)
simple refine (_ _).
Abort.
