(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i $Id$ i*)

Require Import NMinus. (* The most complete file for natural numbers *)
Require Export ZTimesOrder. (* The most complete file for integers *)
Require Export Ring.

Module ZPairsAxiomsMod (Import NAxiomsMod : NAxiomsSig) <: ZAxiomsSig.
Module Import NPropMod := NMinusPropFunct NAxiomsMod. (* Get all properties of natural numbers *)

(* We do not declare ring in Natural/Abstract for two reasons. First, some
of the properties proved in NPlus and NTimes are used in the new BinNat,
and it is in turn used in Ring. Using ring in Natural/Abstract would be
circular. It is possible, however, not to make BinNat dependent on
Numbers/Natural and prove the properties necessary for ring from scratch
(this is, of course, how it used to be). In addition, if we define semiring
structures in the implementation subdirectories of Natural, we are able to
specify binary natural numbers as the type of coefficients. For these
reasons we define an abstract semiring here. *)

Open Local Scope NatScope.

Lemma Nsemi_ring : semi_ring_theory 0 1 plus times Neq.
Proof.
constructor.
exact plus_0_l.
exact plus_comm.
exact plus_assoc.
exact times_1_l.
exact times_0_l.
exact times_comm.
exact times_assoc.
exact times_plus_distr_r.
Qed.

Add Ring NSR : Nsemi_ring.

(* The definitios of functions (NZplus, NZtimes, etc.) will be unfolded by
the properties functor. Since we don't want Zplus_comm to refer to unfolded
definitions of equality: fun p1 p2 : NZ => (fst p1 + snd p2) = (fst p2 + snd p1),
we will provide an extra layer of definitions. *)

Definition Z := (N * N)%type.
Definition Z0 : Z := (0, 0).
Definition Zeq (p1 p2 : Z) := ((fst p1) + (snd p2) == (fst p2) + (snd p1)).
Definition Zsucc (n : Z) : Z := (S (fst n), snd n).
Definition Zpred (n : Z) : Z := (fst n, S (snd n)).

(* We do not have Zpred (Zsucc n) = n but only Zpred (Zsucc n) == n. It
could be possible to consider as canonical only pairs where one of the
elements is 0, and make all operations convert canonical values into other
canonical values. In that case, we could get rid of setoids and arrive at
integers as signed natural numbers. *)

Definition Zplus (n m : Z) : Z := ((fst n) + (fst m), (snd n) + (snd m)).
Definition Zminus (n m : Z) : Z := ((fst n) + (snd m), (snd n) + (fst m)).

(* Unfortunately, the elements of the pair keep increasing, even during
subtraction *)

Definition Ztimes (n m : Z) : Z :=
  ((fst n) * (fst m) + (snd n) * (snd m), (fst n) * (snd m) + (snd n) * (fst m)).
Definition Zlt (n m : Z) := (fst n) + (snd m) < (fst m) + (snd n).
Definition Zle (n m : Z) := (fst n) + (snd m) <= (fst m) + (snd n).
Definition Zmin (n m : Z) := (min ((fst n) + (snd m)) ((fst m) + (snd n)), (snd n) + (snd m)).
Definition Zmax (n m : Z) := (max ((fst n) + (snd m)) ((fst m) + (snd n)), (snd n) + (snd m)).

Delimit Scope IntScope with Int.
Bind Scope IntScope with Z.
Notation "x == y"  := (Zeq x y) (at level 70) : IntScope.
Notation "x ~= y" := (~ Zeq x y) (at level 70) : IntScope.
Notation "0" := Z0 : IntScope.
Notation "1" := (Zsucc Z0) : IntScope.
Notation "x + y" := (Zplus x y) : IntScope.
Notation "x - y" := (Zminus x y) : IntScope.
Notation "x * y" := (Ztimes x y) : IntScope.
Notation "x < y" := (Zlt x y) : IntScope.
Notation "x <= y" := (Zle x y) : IntScope.
Notation "x > y" := (Zlt y x) (only parsing) : IntScope.
Notation "x >= y" := (Zle y x) (only parsing) : IntScope.

Notation Local N := NZ.
(* To remember N without having to use a long qualifying name. since NZ will be redefined *)
Notation Local NE := NZeq (only parsing).
Notation Local plus_wd := NZplus_wd (only parsing).

Module Export NZOrdAxiomsMod <: NZOrdAxiomsSig.
Module Export NZAxiomsMod <: NZAxiomsSig.

Definition NZ : Type := Z.
Definition NZeq := Zeq.
Definition NZ0 := Z0.
Definition NZsucc := Zsucc.
Definition NZpred := Zpred.
Definition NZplus := Zplus.
Definition NZminus := Zminus.
Definition NZtimes := Ztimes.

Theorem ZE_refl : reflexive Z Zeq.
Proof.
unfold reflexive, Zeq. reflexivity.
Qed.

Theorem ZE_symm : symmetric Z Zeq.
Proof.
unfold symmetric, Zeq; now symmetry.
Qed.

Theorem ZE_trans : transitive Z Zeq.
Proof.
unfold transitive, Zeq. intros n m p H1 H2.
assert (H3 : (fst n + snd m) + (fst m + snd p) == (fst m + snd n) + (fst p + snd m))
by now apply plus_wd.
stepl ((fst n + snd p) + (fst m + snd m)) in H3 by ring.
stepr ((fst p + snd n) + (fst m + snd m)) in H3 by ring.
now apply -> plus_cancel_r in H3.
Qed.

Theorem NZeq_equiv : equiv Z Zeq.
Proof.
unfold equiv; repeat split; [apply ZE_refl | apply ZE_trans | apply ZE_symm].
Qed.

Add Relation Z Zeq
 reflexivity proved by (proj1 NZeq_equiv)
 symmetry proved by (proj2 (proj2 NZeq_equiv))
 transitivity proved by (proj1 (proj2 NZeq_equiv))
as NZeq_rel.

Add Morphism (@pair N N) with signature NE ==> NE ==> Zeq as Zpair_wd.
Proof.
intros n1 n2 H1 m1 m2 H2; unfold Zeq; simpl; rewrite H1; now rewrite H2.
Qed.

Add Morphism NZsucc with signature Zeq ==> Zeq as NZsucc_wd.
Proof.
unfold NZsucc, Zeq; intros n m H; simpl.
do 2 rewrite plus_succ_l; now rewrite H.
Qed.

Add Morphism NZpred with signature Zeq ==> Zeq as NZpred_wd.
Proof.
unfold NZpred, Zeq; intros n m H; simpl.
do 2 rewrite plus_succ_r; now rewrite H.
Qed.

Add Morphism NZplus with signature Zeq ==> Zeq ==> Zeq as NZplus_wd.
Proof.
unfold Zeq, NZplus; intros n1 m1 H1 n2 m2 H2; simpl.
assert (H3 : (fst n1 + snd m1) + (fst n2 + snd m2) == (fst m1 + snd n1) + (fst m2 + snd n2))
by now apply plus_wd.
stepl (fst n1 + snd m1 + (fst n2 + snd m2)) by ring.
now stepr (fst m1 + snd n1 + (fst m2 + snd n2)) by ring.
Qed.

Add Morphism NZminus with signature Zeq ==> Zeq ==> Zeq as NZminus_wd.
Proof.
unfold Zeq, NZminus; intros n1 m1 H1 n2 m2 H2; simpl.
symmetry in H2.
assert (H3 : (fst n1 + snd m1) + (fst m2 + snd n2) == (fst m1 + snd n1) + (fst n2 + snd m2))
by now apply plus_wd.
stepl (fst n1 + snd m1 + (fst m2 + snd n2)) by ring.
now stepr (fst m1 + snd n1 + (fst n2 + snd m2)) by ring.
Qed.

Add Morphism NZtimes with signature Zeq ==> Zeq ==> Zeq as NZtimes_wd.
Proof.
unfold NZtimes, Zeq; intros n1 m1 H1 n2 m2 H2; simpl.
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

Section Induction.
Open Scope NatScope. (* automatically closes at the end of the section *)
Variable A : Z -> Prop.
Hypothesis A_wd : predicate_wd Zeq A.

Add Morphism A with signature Zeq ==> iff as A_morph.
Proof.
exact A_wd.
Qed.

Theorem NZinduction :
  A 0 -> (forall n : Z, A n <-> A (Zsucc n)) -> forall n : Z, A n. (* 0 is interpreted as in Z due to "Bind" directive *)
Proof.
intros A0 AS n; unfold NZ0, Zsucc, predicate_wd, fun_wd, Zeq in *.
destruct n as [n m].
cut (forall p : N, A (p, 0)); [intro H1 |].
cut (forall p : N, A (0, p)); [intro H2 |].
destruct (plus_dichotomy n m) as [[p H] | [p H]].
rewrite (A_wd (n, m) (0, p)) by (rewrite plus_0_l; now rewrite plus_comm).
apply H2.
rewrite (A_wd (n, m) (p, 0)) by now rewrite plus_0_r. apply H1.
induct p. assumption. intros p IH.
apply -> (A_wd (0, p) (1, S p)) in IH; [| now rewrite plus_0_l, plus_1_l].
now apply <- AS.
induct p. assumption. intros p IH.
replace 0 with (snd (p, 0)); [| reflexivity].
replace (S p) with (S (fst (p, 0))); [| reflexivity]. now apply -> AS.
Qed.

End Induction.

(* Time to prove theorems in the language of Z *)

Open Local Scope IntScope.

Theorem NZpred_succ : forall n : Z, Zpred (Zsucc n) == n.
Proof.
unfold NZpred, NZsucc, Zeq; intro n; simpl.
rewrite plus_succ_l; now rewrite plus_succ_r.
Qed.

Theorem NZplus_0_l : forall n : Z, 0 + n == n.
Proof.
intro n; unfold NZplus, Zeq; simpl. now do 2 rewrite plus_0_l.
Qed.

Theorem NZplus_succ_l : forall n m : Z, (Zsucc n) + m == Zsucc (n + m).
Proof.
intros n m; unfold NZplus, Zeq; simpl. now do 2 rewrite plus_succ_l.
Qed.

Theorem NZminus_0_r : forall n : Z, n - 0 == n.
Proof.
intro n; unfold NZminus, Zeq; simpl. now do 2 rewrite plus_0_r.
Qed.

Theorem NZminus_succ_r : forall n m : Z, n - (Zsucc m) == Zpred (n - m).
Proof.
intros n m; unfold NZminus, Zeq; simpl. symmetry; now rewrite plus_succ_r.
Qed.

Theorem NZtimes_0_l : forall n : Z, 0 * n == 0.
Proof.
intro n; unfold NZtimes, Zeq; simpl.
repeat rewrite times_0_l. now rewrite plus_assoc.
Qed.

Theorem NZtimes_succ_l : forall n m : Z, (Zsucc n) * m == n * m + m.
Proof.
intros n m; unfold NZtimes, NZsucc, Zeq; simpl.
do 2 rewrite times_succ_l. ring.
Qed.

End NZAxiomsMod.

Definition NZlt := Zlt.
Definition NZle := Zle.
Definition NZmin := Zmin.
Definition NZmax := Zmax.

Add Morphism NZlt with signature Zeq ==> Zeq ==> iff as NZlt_wd.
Proof.
unfold NZlt, Zlt, Zeq; intros n1 m1 H1 n2 m2 H2; simpl. split; intro H.
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

Add Morphism NZle with signature Zeq ==> Zeq ==> iff as NZle_wd.
Proof.
unfold NZle, Zle, Zeq; intros n1 m1 H1 n2 m2 H2; simpl.
do 2 rewrite lt_eq_cases. rewrite (NZlt_wd n1 m1 H1 n2 m2 H2). fold (m1 < m2)%Int.
fold (n1 == n2)%Int (m1 == m2)%Int; fold (n1 == m1)%Int in H1; fold (n2 == m2)%Int in H2.
now rewrite H1, H2.
Qed.

Add Morphism NZmin with signature Zeq ==> Zeq ==> Zeq as NZmin_wd.
Proof.
intros n1 m1 H1 n2 m2 H2; unfold NZmin, Zeq; simpl.
destruct (le_ge_cases (fst n1 + snd n2) (fst n2 + snd n1)) as [H | H].
rewrite (min_l (fst n1 + snd n2) (fst n2 + snd n1)) by assumption.
rewrite (min_l (fst m1 + snd m2) (fst m2 + snd m1)) by
now apply -> (NZle_wd n1 m1 H1 n2 m2 H2).
stepl ((fst n1 + snd m1) + (snd n2 + snd m2)) by ring.
unfold Zeq in H1. rewrite H1. ring.
rewrite (min_r (fst n1 + snd n2) (fst n2 + snd n1)) by assumption.
rewrite (min_r (fst m1 + snd m2) (fst m2 + snd m1)) by
now apply -> (NZle_wd n2 m2 H2 n1 m1 H1).
stepl ((fst n2 + snd m2) + (snd n1 + snd m1)) by ring.
unfold Zeq in H2. rewrite H2. ring.
Qed.

Add Morphism NZmax with signature Zeq ==> Zeq ==> Zeq as NZmax_wd.
Proof.
intros n1 m1 H1 n2 m2 H2; unfold NZmax, Zeq; simpl.
destruct (le_ge_cases (fst n1 + snd n2) (fst n2 + snd n1)) as [H | H].
rewrite (max_r (fst n1 + snd n2) (fst n2 + snd n1)) by assumption.
rewrite (max_r (fst m1 + snd m2) (fst m2 + snd m1)) by
now apply -> (NZle_wd n1 m1 H1 n2 m2 H2).
stepl ((fst n2 + snd m2) + (snd n1 + snd m1)) by ring.
unfold Zeq in H2. rewrite H2. ring.
rewrite (max_l (fst n1 + snd n2) (fst n2 + snd n1)) by assumption.
rewrite (max_l (fst m1 + snd m2) (fst m2 + snd m1)) by
now apply -> (NZle_wd n2 m2 H2 n1 m1 H1).
stepl ((fst n1 + snd m1) + (snd n2 + snd m2)) by ring.
unfold Zeq in H1. rewrite H1. ring.
Qed.

Open Local Scope IntScope.

Theorem NZlt_eq_cases : forall n m : Z, n <= m <-> n < m \/ n == m.
Proof.
intros n m; unfold Zlt, Zle, Zeq; simpl. apply lt_eq_cases.
Qed.

Theorem NZlt_irrefl : forall n : Z, ~ (n < n).
Proof.
intros n; unfold Zlt, Zeq; simpl. apply lt_irrefl.
Qed.

Theorem NZlt_succ_r : forall n m : Z, n < (Zsucc m) <-> n <= m.
Proof.
intros n m; unfold Zlt, Zle, Zeq; simpl. rewrite plus_succ_l; apply lt_succ_r.
Qed.

Theorem NZmin_l : forall n m : Z, n <= m -> Zmin n m == n.
Proof.
unfold Zmin, Zle, Zeq; simpl; intros n m H.
rewrite min_l by assumption. ring.
Qed.

Theorem NZmin_r : forall n m : Z, m <= n -> Zmin n m == m.
Proof.
unfold Zmin, Zle, Zeq; simpl; intros n m H.
rewrite min_r by assumption. ring.
Qed.

Theorem NZmax_l : forall n m : Z, m <= n -> Zmax n m == n.
Proof.
unfold Zmax, Zle, Zeq; simpl; intros n m H.
rewrite max_l by assumption. ring.
Qed.

Theorem NZmax_r : forall n m : Z, n <= m -> Zmax n m == m.
Proof.
unfold Zmax, Zle, Zeq; simpl; intros n m H.
rewrite max_r by assumption. ring.
Qed.

End NZOrdAxiomsMod.

Definition Zopp (n : Z) : Z := (snd n, fst n).

Notation "- x" := (Zopp x) : IntScope.

Add Morphism Zopp with signature Zeq ==> Zeq as Zopp_wd.
Proof.
unfold Zeq; intros n m H; simpl. symmetry.
stepl (fst n + snd m) by apply plus_comm.
now stepr (fst m + snd n) by apply plus_comm.
Qed.

Open Local Scope IntScope.

Theorem Zsucc_pred : forall n : Z, Zsucc (Zpred n) == n.
Proof.
intro n; unfold Zsucc, Zpred, Zeq; simpl.
rewrite plus_succ_l; now rewrite plus_succ_r.
Qed.

Theorem Zopp_0 : - 0 == 0.
Proof.
unfold Zopp, Zeq; simpl. now rewrite plus_0_l.
Qed.

Theorem Zopp_succ : forall n, - (Zsucc n) == Zpred (- n).
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

