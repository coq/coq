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

(* Proposed by Jean-Christophe Filliâtre: confusion between an Omega *)
(* internal variable and a section variable (June 2001) *)

Section A.
Variable x,y : Z.
Hypothesis H : `x > y`.
Lemma lem4 : `x > y`.
Omega.
Qed.
End A.

(* Proposed by Yves Bertot: because a section var, L was wrongly renamed L0 *)
(* May 2002 *)

Section B.
Variables R1,R2,S1,S2,H,S:Z.
Hypothesis I:`R1 < 0`->`R2 = R1+(2*S1-1)`.
Hypothesis J:`R1 < 0`->`S2 = S1-1`.
Hypothesis K:`R1 >= 0`->`R2 = R1`.
Hypothesis L:`R1 >= 0`->`S2 = S1`.
Hypothesis M:`H <= 2*S`.
Hypothesis N:`S < H`.
Lemma lem5 : `H > 0`.
Omega.
Qed.
End B.

(* From Nicolas Oury (bug #180): handling -> on Set (fixed Oct 2002) *)
Lemma lem4: (A: Set) (i:Z) `i<= 0` -> (`i<= 0` -> A) -> `i<=0`.
Intros.
Omega.
Qed.

(* Adapted from an example in Nijmegen/FTA/ftc/RefSeparating (Oct 2002) *)
Require Omega.
Section C.
Parameter g:(m:nat)~m=O->Prop.
Parameter f:(m:nat)(H:~m=O)(g m H).
Variable n:nat.
Variable ap_n:~n=O.
Local delta:=(f n ap_n).
Lemma lem6 : n=n.
Omega.
Qed.
End C.

(* Problem of dependencies *)
Require Omega.
Lemma lem7 : (H:O=O->O=O) H=H -> O=O.
Intros; Omega.
Qed.


