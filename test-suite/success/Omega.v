(* Submitted by Xavier Urbain 18 Jan 2002 *)

Require Omega.
Lemma lem : (x,y:Z) 
  `-5 < x < 5` ->
  `-5 < y` ->
  `-5 < x+y+5`.
Proof.
Intros x y.
Omega.
Qed.
