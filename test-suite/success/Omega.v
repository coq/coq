Require Omega.

(* Submitted by Xavier Urbain 18 Jan 2002 *)

Lemma lem1 : (x,y:Z) 
  `-5 < x < 5` ->
  `-5 < y` ->
  `-5 < x+y+5`.
Proof.
Intros x y.
Omega.
Qed.

(* Proposed by Pierre Crégut *)

Lemma lem2 : (x:Z) `x < 4` -> `x > 2` -> `x=3`.
Intro.
Omega.
Qed.

(* Proposed by Jean-Christophe Filliâtre *)

Lemma lem3 : (x,y:Z) `x = y` -> `x+x = y+y`.
Proof.
Intros.
Omega.
Qed.
