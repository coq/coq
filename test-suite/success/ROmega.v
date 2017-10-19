
Require Import ZArith ROmega.

(* Submitted by Xavier Urbain 18 Jan 2002 *)

Lemma lem1 :
 forall x y : Z, (-5 < x < 5)%Z -> (-5 < y)%Z -> (-5 < x + y + 5)%Z.
Proof.
intros x y.
romega.
Qed.

(* Proposed by Pierre Crégut *)

Lemma lem2 : forall x : Z, (x < 4)%Z -> (x > 2)%Z -> x = 3%Z.
intro.
 romega.
Qed.

(* Proposed by Jean-Christophe Filliâtre *)

Lemma lem3 : forall x y : Z, x = y -> (x + x)%Z = (y + y)%Z.
Proof.
intros.
romega.
Qed.

(* Proposed by Jean-Christophe Filliâtre: confusion between an Omega *)
(* internal variable and a section variable (June 2001) *)

Section A.
Variable x y : Z.
Hypothesis H : (x > y)%Z.
Lemma lem4 : (x > y)%Z.
 romega.
Qed.
End A.

(* Proposed by Yves Bertot: because a section var, L was wrongly renamed L0 *)
(* May 2002 *)

Section B.
Variable R1 R2 S1 S2 H S : Z.
Hypothesis I : (R1 < 0)%Z -> R2 = (R1 + (2 * S1 - 1))%Z.
Hypothesis J : (R1 < 0)%Z -> S2 = (S1 - 1)%Z.
Hypothesis K : (R1 >= 0)%Z -> R2 = R1.
Hypothesis L : (R1 >= 0)%Z -> S2 = S1.
Hypothesis M : (H <= 2 * S)%Z.
Hypothesis N : (S < H)%Z.
Lemma lem5 : (H > 0)%Z.
 romega.
Qed.
End B.

(* From Nicolas Oury (BZ#180): handling -> on Set (fixed Oct 2002) *)
Lemma lem6 :
 forall (A : Set) (i : Z), (i <= 0)%Z -> ((i <= 0)%Z -> A) -> (i <= 0)%Z.
intros.
 romega.
Qed.

(* Adapted from an example in Nijmegen/FTA/ftc/RefSeparating (Oct 2002) *)
Require Import Omega.
Section C.
Parameter g : forall m : nat, m <> 0 -> Prop.
Parameter f : forall (m : nat) (H : m <> 0), g m H.
Variable n : nat.
Variable ap_n : n <> 0.
Let delta := f n ap_n.
Lemma lem7 : n = n.
 romega with nat.
Qed.
End C.

(* Problem of dependencies *)
Require Import Omega.
Lemma lem8 : forall H : 0 = 0 -> 0 = 0, H = H -> 0 = 0.
intros.
romega with nat.
Qed.

(* Bug that what caused by the use of intro_using in Omega *)
Require Import Omega.
Lemma lem9 :
 forall p q : nat, ~ (p <= q /\ p < q \/ q <= p /\ p < q) -> p < p \/ p <= p.
intros.
romega with nat.
Qed.

(* Check that the interpretation of mult on nat enforces its positivity *)
(* Submitted by Hubert Thierry (BZ#743) *)
(* Postponed... problem with goals of the form "(n*m=0)%nat -> (n*m=0)%Z" *)
Lemma lem10 : forall n m : nat, le n (plus n (mult n m)).
Proof.
intros; romega with nat.
Qed.
