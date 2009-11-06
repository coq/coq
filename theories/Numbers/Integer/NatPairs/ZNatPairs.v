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

Require Import NSub. (* The most complete file for natural numbers *)
Require Export ZMulOrder. (* The most complete file for integers *)
Require Export Ring.

Module ZPairsAxiomsMod (Import NAxiomsMod : NAxiomsSig) <: ZAxiomsSig.
Module Import NPropMod := NSubPropFunct NAxiomsMod. (* Get all properties of natural numbers *)

(* We do not declare ring in Natural/Abstract for two reasons. First, some
of the properties proved in NAdd and NMul are used in the new BinNat,
and it is in turn used in Ring. Using ring in Natural/Abstract would be
circular. It is possible, however, not to make BinNat dependent on
Numbers/Natural and prove the properties necessary for ring from scratch
(this is, of course, how it used to be). In addition, if we define semiring
structures in the implementation subdirectories of Natural, we are able to
specify binary natural numbers as the type of coefficients. For these
reasons we define an abstract semiring here. *)

Open Local Scope NatScope.

Lemma Nsemi_ring : semi_ring_theory 0 1 add mul Neq.
Proof.
constructor.
exact add_0_l.
exact add_comm.
exact add_assoc.
exact mul_1_l.
exact mul_0_l.
exact mul_comm.
exact mul_assoc.
exact mul_add_distr_r.
Qed.

Add Ring NSR : Nsemi_ring.

(* The definitions of functions (NZadd, NZmul, etc.) will be unfolded by
the properties functor. Since we don't want Zadd_comm to refer to unfolded
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

Definition Zadd (n m : Z) : Z := ((fst n) + (fst m), (snd n) + (snd m)).
Definition Zsub (n m : Z) : Z := ((fst n) + (snd m), (snd n) + (fst m)).

(* Unfortunately, the elements of the pair keep increasing, even during
subtraction *)

Definition Zmul (n m : Z) : Z :=
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
Notation "x + y" := (Zadd x y) : IntScope.
Notation "x - y" := (Zsub x y) : IntScope.
Notation "x * y" := (Zmul x y) : IntScope.
Notation "x < y" := (Zlt x y) : IntScope.
Notation "x <= y" := (Zle x y) : IntScope.
Notation "x > y" := (Zlt y x) (only parsing) : IntScope.
Notation "x >= y" := (Zle y x) (only parsing) : IntScope.

Notation Local N := NZ.
(* To remember N without having to use a long qualifying name. since NZ will be redefined *)
Notation Local NE := NZeq (only parsing).
Notation Local add_wd := NZadd_wd (only parsing).

Module Export NZOrdAxiomsMod <: NZOrdAxiomsSig.
Module Export NZAxiomsMod <: NZAxiomsSig.

Definition NZ : Type := Z.
Definition NZeq := Zeq.
Definition NZ0 := Z0.
Definition NZsucc := Zsucc.
Definition NZpred := Zpred.
Definition NZadd := Zadd.
Definition NZsub := Zsub.
Definition NZmul := Zmul.

Theorem ZE_refl : reflexive Z Zeq.
Proof.
unfold reflexive, Zeq. reflexivity.
Qed.

Theorem ZE_sym : symmetric Z Zeq.
Proof.
unfold symmetric, Zeq; now symmetry.
Qed.

Theorem ZE_trans : transitive Z Zeq.
Proof.
unfold transitive, Zeq. intros n m p H1 H2.
assert (H3 : (fst n + snd m) + (fst m + snd p) == (fst m + snd n) + (fst p + snd m))
by now apply add_wd.
stepl ((fst n + snd p) + (fst m + snd m)) in H3 by ring.
stepr ((fst p + snd n) + (fst m + snd m)) in H3 by ring.
now apply -> add_cancel_r in H3.
Qed.

Instance NZeq_equiv : Equivalence Zeq.
Proof.
split; [apply ZE_refl | apply ZE_sym | apply ZE_trans].
Qed.

Instance Zpair_wd : Proper (NE==>NE==>Zeq) (@pair N N).
Proof.
intros n1 n2 H1 m1 m2 H2; unfold Zeq; simpl; rewrite H1; now rewrite H2.
Qed.

Instance NZsucc_wd : Proper (Zeq ==> Zeq) NZsucc.
Proof.
unfold NZsucc, Zeq; intros n m H; simpl.
do 2 rewrite add_succ_l; now rewrite H.
Qed.

Instance NZpred_wd : Proper (Zeq ==> Zeq) NZpred.
Proof.
unfold NZpred, Zeq; intros n m H; simpl.
do 2 rewrite add_succ_r; now rewrite H.
Qed.

Instance NZadd_wd : Proper (Zeq ==> Zeq ==> Zeq) NZadd.
Proof.
unfold Zeq, NZadd; intros n1 m1 H1 n2 m2 H2; simpl.
assert (H3 : (fst n1 + snd m1) + (fst n2 + snd m2) == (fst m1 + snd n1) + (fst m2 + snd n2))
by now apply add_wd.
stepl (fst n1 + snd m1 + (fst n2 + snd m2)) by ring.
now stepr (fst m1 + snd n1 + (fst m2 + snd n2)) by ring.
Qed.

Instance NZsub_wd : Proper (Zeq ==> Zeq ==> Zeq) NZsub.
Proof.
unfold Zeq, NZsub; intros n1 m1 H1 n2 m2 H2; simpl.
symmetry in H2.
assert (H3 : (fst n1 + snd m1) + (fst m2 + snd n2) == (fst m1 + snd n1) + (fst n2 + snd m2))
by now apply add_wd.
stepl (fst n1 + snd m1 + (fst m2 + snd n2)) by ring.
now stepr (fst m1 + snd n1 + (fst n2 + snd m2)) by ring.
Qed.

Instance NZmul_wd : Proper (Zeq ==> Zeq ==> Zeq) NZmul.
Proof.
unfold NZmul, Zeq; intros n1 m1 H1 n2 m2 H2; simpl.
stepl (fst n1 * fst n2 + (snd n1 * snd n2 + fst m1 * snd m2 + snd m1 * fst m2)) by ring.
stepr (fst n1 * snd n2 + (fst m1 * fst m2 + snd m1 * snd m2 + snd n1 * fst n2)) by ring.
apply add_mul_repl_pair with (n := fst m2) (m := snd m2); [| now idtac].
stepl (snd n1 * snd n2 + (fst n1 * fst m2 + fst m1 * snd m2 + snd m1 * fst m2)) by ring.
stepr (snd n1 * fst n2 + (fst n1 * snd m2 + fst m1 * fst m2 + snd m1 * snd m2)) by ring.
apply add_mul_repl_pair with (n := snd m2) (m := fst m2);
[| (stepl (fst n2 + snd m2) by ring); now stepr (fst m2 + snd n2) by ring].
stepl (snd m2 * snd n1 + (fst n1 * fst m2 + fst m1 * snd m2 + snd m1 * fst m2)) by ring.
stepr (snd m2 * fst n1 + (snd n1 * fst m2 + fst m1 * fst m2 + snd m1 * snd m2)) by ring.
apply add_mul_repl_pair with (n := snd m1) (m := fst m1);
[ | (stepl (fst n1 + snd m1) by ring); now stepr (fst m1 + snd n1) by ring].
stepl (fst m2 * fst n1 + (snd m2 * snd m1 + fst m1 * snd m2 + snd m1 * fst m2)) by ring.
stepr (fst m2 * snd n1 + (snd m2 * fst m1 + fst m1 * fst m2 + snd m1 * snd m2)) by ring.
apply add_mul_repl_pair with (n := fst m1) (m := snd m1); [| now idtac].
ring.
Qed.

Section Induction.
Open Scope NatScope. (* automatically closes at the end of the section *)
Variable A : Z -> Prop.
Hypothesis A_wd : Proper (Zeq==>iff) A.

Theorem NZinduction :
  A 0 -> (forall n : Z, A n <-> A (Zsucc n)) -> forall n : Z, A n.
  (* 0 is interpreted as in Z due to "Bind" directive *)
Proof.
intros A0 AS n; unfold NZ0, Zsucc, Zeq in *.
destruct n as [n m].
cut (forall p : N, A (p, 0)); [intro H1 |].
cut (forall p : N, A (0, p)); [intro H2 |].
destruct (add_dichotomy n m) as [[p H] | [p H]].
rewrite (A_wd (n, m) (0, p)) by (rewrite add_0_l; now rewrite add_comm).
apply H2.
rewrite (A_wd (n, m) (p, 0)) by now rewrite add_0_r. apply H1.
induct p. assumption. intros p IH.
apply -> (A_wd (0, p) (1, S p)) in IH; [| now rewrite add_0_l, add_1_l].
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
rewrite add_succ_l; now rewrite add_succ_r.
Qed.

Theorem NZadd_0_l : forall n : Z, 0 + n == n.
Proof.
intro n; unfold NZadd, Zeq; simpl. now do 2 rewrite add_0_l.
Qed.

Theorem NZadd_succ_l : forall n m : Z, (Zsucc n) + m == Zsucc (n + m).
Proof.
intros n m; unfold NZadd, Zeq; simpl. now do 2 rewrite add_succ_l.
Qed.

Theorem NZsub_0_r : forall n : Z, n - 0 == n.
Proof.
intro n; unfold NZsub, Zeq; simpl. now do 2 rewrite add_0_r.
Qed.

Theorem NZsub_succ_r : forall n m : Z, n - (Zsucc m) == Zpred (n - m).
Proof.
intros n m; unfold NZsub, Zeq; simpl. symmetry; now rewrite add_succ_r.
Qed.

Theorem NZmul_0_l : forall n : Z, 0 * n == 0.
Proof.
intro n; unfold NZmul, Zeq; simpl.
repeat rewrite mul_0_l. now rewrite add_assoc.
Qed.

Theorem NZmul_succ_l : forall n m : Z, (Zsucc n) * m == n * m + m.
Proof.
intros n m; unfold NZmul, NZsucc, Zeq; simpl.
do 2 rewrite mul_succ_l. ring.
Qed.

End NZAxiomsMod.

Definition NZlt := Zlt.
Definition NZle := Zle.
Definition NZmin := Zmin.
Definition NZmax := Zmax.

Instance NZlt_wd : Proper (Zeq ==> Zeq ==> iff) NZlt.
Proof.
unfold NZlt, Zlt, Zeq; intros n1 m1 H1 n2 m2 H2; simpl. split; intro H.
stepr (snd m1 + fst m2) by apply add_comm.
apply (add_lt_repl_pair (fst n1) (snd n1)); [| assumption].
stepl (snd m2 + fst n1) by apply add_comm.
stepr (fst m2 + snd n1) by apply add_comm.
apply (add_lt_repl_pair (snd n2) (fst n2)).
now stepl (fst n1 + snd n2) by apply add_comm.
stepl (fst m2 + snd n2) by apply add_comm. now stepr (fst n2 + snd m2) by apply add_comm.
stepr (snd n1 + fst n2) by apply add_comm.
apply (add_lt_repl_pair (fst m1) (snd m1)); [| now symmetry].
stepl (snd n2 + fst m1) by apply add_comm.
stepr (fst n2 + snd m1) by apply add_comm.
apply (add_lt_repl_pair (snd m2) (fst m2)).
now stepl (fst m1 + snd m2) by apply add_comm.
stepl (fst n2 + snd m2) by apply add_comm. now stepr (fst m2 + snd n2) by apply add_comm.
Qed.

Instance NZle_wd : Proper (Zeq ==> Zeq ==> iff) NZle.
Proof.
unfold NZle, Zle, Zeq; intros n1 m1 H1 n2 m2 H2; simpl.
do 2 rewrite lt_eq_cases. rewrite (NZlt_wd n1 m1 H1 n2 m2 H2). fold (m1 < m2)%Int.
fold (n1 == n2)%Int (m1 == m2)%Int; fold (n1 == m1)%Int in H1; fold (n2 == m2)%Int in H2.
now rewrite H1, H2.
Qed.

Instance NZmin_wd : Proper (Zeq ==> Zeq ==> Zeq) NZmin.
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

Instance NZmax_wd : Proper (Zeq ==> Zeq ==> Zeq) NZmax.
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
intros n m; unfold Zlt, Zle, Zeq; simpl. rewrite add_succ_l; apply lt_succ_r.
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

Instance Zopp_wd : Proper (Zeq ==> Zeq) Zopp.
Proof.
unfold Zeq; intros n m H; simpl. symmetry.
stepl (fst n + snd m) by apply add_comm.
now stepr (fst m + snd n) by apply add_comm.
Qed.

Open Local Scope IntScope.

Theorem Zsucc_pred : forall n : Z, Zsucc (Zpred n) == n.
Proof.
intro n; unfold Zsucc, Zpred, Zeq; simpl.
rewrite add_succ_l; now rewrite add_succ_r.
Qed.

Theorem Zopp_0 : - 0 == 0.
Proof.
unfold Zopp, Zeq; simpl. now rewrite add_0_l.
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
Module Export ZPairsMulOrderPropMod := ZMulOrderPropFunct ZPairsPeanoAxiomsMod.

Open Local Scope IntScope.

Eval compute in (3, 5) * (4, 6).
*)

