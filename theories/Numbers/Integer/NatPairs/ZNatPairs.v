Require Import NMinus. (* The most complete file for natural numbers *)
Require Import ZTimesOrder. (* The most complete file for integers *)

Module ZPairsAxiomsMod (Import NAxiomsMod : NAxiomsSig) <: ZAxiomsSig.
Module Import NPropMod := NMinusPropFunct NAxiomsMod. (* Get all properties of natural numbers *)
Notation Local N := NZ. (* To remember N without having to use a long qualifying name *)
Notation Local NE := NZE (only parsing).
Notation Local plus_wd := NZplus_wd (only parsing).
Open Local Scope NatIntScope.

Module Export NZOrdAxiomsMod <: NZOrdAxiomsSig.
Module Export NZAxiomsMod <: NZAxiomsSig.

Definition NZ : Set := (NZ * NZ)%type.
Definition NZE (p1 p2 : NZ) := ((fst p1) + (snd p2) == (fst p2) + (snd p1)).
Notation Z := NZ (only parsing).
Notation E := NZE (only parsing).
Definition NZ0 := (0, 0).
Definition NZsucc (n : Z) := (S (fst n), snd n).
Definition NZpred (n : Z) := (fst n, S (snd n)).
(* We do not have P (S n) = n but only P (S n) == n. It could be possible
to consider as canonical only pairs where one of the elements is 0, and
make all operations convert canonical values into other canonical values.
In that case, we could get rid of setoids as well as arrive at integers as
signed natural numbers. *)
Definition NZplus (n m : Z) := ((fst n) + (fst m), (snd n) + (snd m)).
Definition NZminus (n m : Z) := ((fst n) + (snd m), (snd n) + (fst m)).
Definition NZuminus (n : Z) := (snd n, fst n).
(* Unfortunately, the elements of the pair keep increasing, even during
subtraction *)
Definition NZtimes (n m : Z) :=
  ((fst n) * (fst m) + (snd n) * (snd m), (fst n) * (snd m) + (snd n) * (fst m)).

Theorem ZE_refl : reflexive Z E.
Proof.
unfold reflexive, E; reflexivity.
Qed.

Theorem ZE_symm : symmetric Z E.
Proof.
unfold symmetric, E; now symmetry.
Qed.

Theorem ZE_trans : transitive Z E.
Proof.
unfold transitive, E. intros n m p H1 H2.
assert (H3 : (fst n + snd m) + (fst m + snd p) == (fst m + snd n) + (fst p + snd m))
by now apply plus_wd.
stepl ((fst n + snd p) + (fst m + snd m)) in H3 by ring.
stepr ((fst p + snd n) + (fst m + snd m)) in H3 by ring.
now apply -> plus_cancel_r in H3.
Qed.

Theorem NZE_equiv : equiv Z E.
Proof.
unfold equiv; repeat split; [apply ZE_refl | apply ZE_trans | apply ZE_symm].
Qed.

Add Relation Z E
 reflexivity proved by (proj1 NZE_equiv)
 symmetry proved by (proj2 (proj2 NZE_equiv))
 transitivity proved by (proj1 (proj2 NZE_equiv))
as NZE_rel.

Add Morphism (@pair N N) with signature NE ==> NE ==> E as Zpair_wd.
Proof.
intros n1 n2 H1 m1 m2 H2; unfold E; simpl; rewrite H1; now rewrite H2.
Qed.

Add Morphism NZsucc with signature E ==> E as NZsucc_wd.
Proof.
unfold NZsucc, E; intros n m H; simpl.
do 2 rewrite plus_succ_l; now rewrite H.
Qed.

Add Morphism NZpred with signature E ==> E as NZpred_wd.
Proof.
unfold NZpred, E; intros n m H; simpl.
do 2 rewrite plus_succ_r; now rewrite H.
Qed.

Add Morphism NZplus with signature E ==> E ==> E as NZplus_wd.
Proof.
unfold E, NZplus; intros n1 m1 H1 n2 m2 H2; simpl.
assert (H3 : (fst n1 + snd m1) + (fst n2 + snd m2) == (fst m1 + snd n1) + (fst m2 + snd n2))
by now apply plus_wd.
stepl (fst n1 + snd m1 + (fst n2 + snd m2)) by ring.
now stepr (fst m1 + snd n1 + (fst m2 + snd n2)) by ring.
Qed.

Add Morphism NZminus with signature E ==> E ==> E as NZminus_wd.
Proof.
unfold E, NZminus; intros n1 m1 H1 n2 m2 H2; simpl.
symmetry in H2.
assert (H3 : (fst n1 + snd m1) + (fst m2 + snd n2) == (fst m1 + snd n1) + (fst n2 + snd m2))
by now apply plus_wd.
stepl (fst n1 + snd m1 + (fst m2 + snd n2)) by ring.
now stepr (fst m1 + snd n1 + (fst n2 + snd m2)) by ring.
Qed.

Add Morphism NZtimes with signature E ==> E ==> E as NZtimes_wd.
Proof.
unfold NZtimes, E; intros n1 m1 H1 n2 m2 H2; simpl.
stepl (fst n1 * fst n2 + (snd n1 * snd n2 + fst m1 * snd m2 + snd m1 * fst m2)) by ring.
stepr (fst n1 * snd n2 + (fst m1 * fst m2 + snd m1 * snd m2 + snd n1 * fst n2)) by ring.
apply plus_times_repl_pair with (n := fst m2) (m := snd m2); [| now idtac].
stepl (snd n1 * snd n2 + (fst n1 * fst m2 + fst m1 * snd m2 + snd m1 * fst m2)) by ring.
stepr (snd n1 * fst n2 + (fst n1 * snd m2 + fst m1 * fst m2 + snd m1 * snd m2)) by ring.
apply plus_times_repl_pair with (n := snd m2) (m := fst m2);
[| (stepl (fst n2 + snd m2) by ring); now stepr (fst m2 + snd n2) by ring].
stepl (snd m2 * snd n1 + (fst n1 * fst m2 + fst m1 * snd m2 + snd m1 * fst m2)) by ring.
stepr (snd m2 * fst n1 + (snd n1 * fst m2 + fst m1 * fst m2 + snd m1 * snd m2)) by ring.
apply plus_times_repl_pair with (n := snd m1) (m := fst m1);
[ | (stepl (fst n1 + snd m1) by ring); now stepr (fst m1 + snd n1) by ring].
stepl (fst m2 * fst n1 + (snd m2 * snd m1 + fst m1 * snd m2 + snd m1 * fst m2)) by ring.
stepr (fst m2 * snd n1 + (snd m2 * fst m1 + fst m1 * fst m2 + snd m1 * snd m2)) by ring.
apply plus_times_repl_pair with (n := fst m1) (m := snd m1); [| now idtac].
ring.
Qed.

Delimit Scope IntScope with Int.
Bind Scope IntScope with NZ.
Open Local Scope IntScope.
Notation "x == y"  := (NZE x y) (at level 70) : IntScope.
Notation "x ~= y" := (~ NZE x y) (at level 70) : IntScope.
Notation "0" := NZ0 : IntScope.
Notation "'S'" := NZsucc : IntScope.
Notation "'P'" := NZpred : IntScope.
Notation "1" := (S 0) : IntScope.
Notation "x + y" := (NZplus x y) : IntScope.
Notation "x - y" := (NZminus x y) : IntScope.
Notation "x * y" := (NZtimes x y) : IntScope.

Theorem NZpred_succ : forall n : Z, P (S n) == n.
Proof.
unfold NZpred, NZsucc, E; intro n; simpl.
rewrite plus_succ_l; now rewrite plus_succ_r.
Qed.

Section Induction.
Open Scope NatIntScope. (* automatically closes at the end of the section *)
Variable A : Z -> Prop.
Hypothesis A_wd : predicate_wd E A.

Add Morphism A with signature E ==> iff as A_morph.
Proof.
exact A_wd.
Qed.

Theorem NZinduction :
  A 0 -> (forall n : Z, A n <-> A (S n)) -> forall n : Z, A n. (* 0 is interpreted as in Z due to "Bind" directive *)
Proof.
intros A0 AS n; unfold NZ0, NZsucc, predicate_wd, fun_wd, E in *.
destruct n as [n m].
cut (forall p : N, A (p, 0)); [intro H1 |].
cut (forall p : N, A (0, p)); [intro H2 |].
destruct (plus_dichotomy n m) as [[p H] | [p H]].
rewrite (A_wd (n, m) (0, p)); simpl. rewrite plus_0_l; now rewrite plus_comm. apply H2.
rewrite (A_wd (n, m) (p, 0)); simpl. now rewrite plus_0_r. apply H1.
induct p. assumption. intros p IH.
apply -> (A_wd (0, p) (1, S p)) in IH; [| now rewrite plus_0_l, plus_1_l].
now apply <- AS.
induct p. assumption. intros p IH.
replace 0 with (snd (p, 0)); [| reflexivity].
replace (S p) with (S (fst (p, 0))); [| reflexivity]. now apply -> AS.
Qed.

End Induction.

Theorem NZplus_0_l : forall n : Z, 0 + n == n.
Proof.
intro n; unfold NZplus, E; simpl. now do 2 rewrite plus_0_l.
Qed.

Theorem NZplus_succ_l : forall n m : Z, (S n) + m == S (n + m).
Proof.
intros n m; unfold NZplus, E; simpl. now do 2 rewrite plus_succ_l.
Qed.

Theorem NZminus_0_r : forall n : Z, n - 0 == n.
Proof.
intro n; unfold NZminus, E; simpl. now do 2 rewrite plus_0_r.
Qed.

Theorem NZminus_succ_r : forall n m : Z, n - (S m) == P (n - m).
Proof.
intros n m; unfold NZminus, E; simpl. symmetry; now rewrite plus_succ_r.
Qed.

Theorem NZtimes_0_r : forall n : Z, n * 0 == 0.
Proof.
intro n; unfold NZtimes, E; simpl.
repeat rewrite times_0_r. now rewrite plus_assoc.
Qed.

Theorem NZtimes_succ_r : forall n m : Z, n * (S m) == n * m + n.
Proof.
intros n m; unfold NZtimes, NZsucc, E; simpl.
do 2 rewrite times_succ_r. ring.
Qed.

End NZAxiomsMod.

Definition NZlt (n m : Z) := (fst n) + (snd m) < (fst m) + (snd n).
Definition NZle (n m : Z) := (fst n) + (snd m) <= (fst m) + (snd n).

Notation "x < y" := (NZlt x y) : IntScope.
Notation "x <= y" := (NZle x y) : IntScope.
Notation "x > y" := (NZlt y x) (only parsing) : IntScope.
Notation "x >= y" := (NZle y x) (only parsing) : IntScope.

Add Morphism NZlt with signature E ==> E ==> iff as NZlt_wd.
Proof.
unfold NZlt, E; intros n1 m1 H1 n2 m2 H2; simpl. split; intro H.
stepr (snd m1 + fst m2) by apply plus_comm.
apply (plus_lt_repl_pair (fst n1) (snd n1)); [| assumption].
stepl (snd m2 + fst n1) by apply plus_comm.
stepr (fst m2 + snd n1) by apply plus_comm.
apply (plus_lt_repl_pair (snd n2) (fst n2)).
now stepl (fst n1 + snd n2) by apply plus_comm.
stepl (fst m2 + snd n2) by apply plus_comm. now stepr (fst n2 + snd m2) by apply plus_comm.
stepr (snd n1 + fst n2) by apply plus_comm.
apply (plus_lt_repl_pair (fst m1) (snd m1)); [| now symmetry].
stepl (snd n2 + fst m1) by apply plus_comm.
stepr (fst n2 + snd m1) by apply plus_comm.
apply (plus_lt_repl_pair (snd m2) (fst m2)).
now stepl (fst m1 + snd m2) by apply plus_comm.
stepl (fst n2 + snd m2) by apply plus_comm. now stepr (fst m2 + snd n2) by apply plus_comm.
Qed.

Open Local Scope IntScope.

Add Morphism NZle with signature E ==> E ==> iff as NZle_wd.
Proof.
unfold NZle, E; intros n1 m1 H1 n2 m2 H2; simpl.
do 2 rewrite le_lt_or_eq. rewrite (NZlt_wd n1 m1 H1 n2 m2 H2). fold (m1 < m2).
fold (n1 == n2) (m1 == m2); fold (n1 == m1) in H1; fold (n2 == m2) in H2.
now rewrite H1, H2.
Qed.

Theorem NZle_lt_or_eq : forall n m : Z, n <= m <-> n < m \/ n == m.
Proof.
intros n m; unfold NZlt, NZle, E; simpl. apply le_lt_or_eq.
Qed.

Theorem NZlt_irrefl : forall n : Z, ~ (n < n).
Proof.
intros n; unfold NZlt, E; simpl. apply lt_irrefl.
Qed.

Theorem NZlt_succ_le : forall n m : Z, n < (S m) <-> n <= m.
Proof.
intros n m; unfold NZlt, NZle, E; simpl. rewrite plus_succ_l; apply lt_succ_le.
Qed.

End NZOrdAxiomsMod.

Definition Zopp (n : Z) := (snd n, fst n).

Notation "- x" := (Zopp x) (at level 35, right associativity) : IntScope.

Add Morphism Zopp with signature E ==> E as Zopp_wd.
Proof.
unfold E; intros n m H; simpl. symmetry.
stepl (fst n + snd m) by apply plus_comm.
now stepr (fst m + snd n) by apply plus_comm.
Qed.

Open Local Scope IntScope.

Theorem Zsucc_pred : forall n : Z, S (P n) == n.
Proof.
intro n; unfold NZsucc, NZpred, E; simpl.
rewrite plus_succ_l; now rewrite plus_succ_r.
Qed.

Theorem Zopp_0 : - 0 == 0.
Proof.
unfold Zopp, E; simpl. now rewrite plus_0_l.
Qed.

Theorem Zopp_succ : forall n, - (S n) == P (- n).
Proof.
reflexivity.
Qed.

End ZPairsAxiomsMod.

(* For example, let's build integers out of pairs of Peano natural numbers
and get their properties *)

(* The following lines increase the compilation time at least twice *)
(*
Require Import NPeano.

Module Export ZPairsPeanoAxiomsMod := ZPairsAxiomsMod NPeanoAxiomsMod.
Module Export ZPairsTimesOrderPropMod := ZTimesOrderPropFunct ZPairsPeanoAxiomsMod.

Open Local Scope IntScope.

Eval compute in (3, 5) * (4, 6).
*)

