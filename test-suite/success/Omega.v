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

(* Proposed by Yves Bertot: because a section var, L was wrongly renamed L0 *)
Section A.
Variables R1,R2,S1,S2,H,S:Z.
Hypothesis I:`R1 < 0`->`R2 = R1+(2*S1-1)`.
Hypothesis J:`R1 < 0`->`S2 = S1-1`.
Hypothesis K:`R1 >= 0`->`R2 = R1`.
Hypothesis L:`R1 >= 0`->`S2 = S1`.
Hypothesis M:`H <= 2*S`.
Hypothesis N:`S < H`.
Lemma lem4 : `H > 0`.
Omega.
Qed.
End A.
