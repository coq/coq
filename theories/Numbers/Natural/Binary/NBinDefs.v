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

Require Import BinPos.
Require Export BinNat.
Require Import NSub.

Open Local Scope N_scope.

(** Implementation of [NAxiomsSig] module type via [BinNat.N] *)

Module NBinaryAxiomsMod <: NAxiomsSig.
Module Export NZOrdAxiomsMod <: NZOrdAxiomsSig.
Module Export NZAxiomsMod <: NZAxiomsSig.

Definition NZ := N.
Definition NZeq := @eq N.
Definition NZ0 := N0.
Definition NZsucc := Nsucc.
Definition NZpred := Npred.
Definition NZadd := Nplus.
Definition NZsub := Nminus.
Definition NZmul := Nmult.

Instance NZeq_equiv : Equivalence NZeq.

Add Morphism NZsucc with signature NZeq ==> NZeq as NZsucc_wd.
Proof.
congruence.
Qed.

Add Morphism NZpred with signature NZeq ==> NZeq as NZpred_wd.
Proof.
congruence.
Qed.

Add Morphism NZadd with signature NZeq ==> NZeq ==> NZeq as NZadd_wd.
Proof.
congruence.
Qed.

Add Morphism NZsub with signature NZeq ==> NZeq ==> NZeq as NZsub_wd.
Proof.
congruence.
Qed.

Add Morphism NZmul with signature NZeq ==> NZeq ==> NZeq as NZmul_wd.
Proof.
congruence.
Qed.

Theorem NZinduction :
  forall A : NZ -> Prop, predicate_wd NZeq A ->
    A N0 -> (forall n, A n <-> A (NZsucc n)) -> forall n : NZ, A n.
Proof.
intros A A_wd A0 AS. apply Nrect. assumption. intros; now apply -> AS.
Qed.

Theorem NZpred_succ : forall n : NZ, NZpred (NZsucc n) = n.
Proof.
destruct n as [| p]; simpl. reflexivity.
case_eq (Psucc p); try (intros q H; rewrite <- H; now rewrite Ppred_succ).
intro H; false_hyp H Psucc_not_one.
Qed.

Theorem NZadd_0_l : forall n : NZ, N0 + n = n.
Proof.
reflexivity.
Qed.

Theorem NZadd_succ_l : forall n m : NZ, (NZsucc n) + m = NZsucc (n + m).
Proof.
destruct n; destruct m.
simpl in |- *; reflexivity.
unfold NZsucc, NZadd, Nsucc, Nplus. rewrite <- Pplus_one_succ_l; reflexivity.
simpl in |- *; reflexivity.
simpl in |- *; rewrite Pplus_succ_permute_l; reflexivity.
Qed.

Theorem NZsub_0_r : forall n : NZ, n - N0 = n.
Proof.
now destruct n.
Qed.

Theorem NZsub_succ_r : forall n m : NZ, n - (NZsucc m) = NZpred (n - m).
Proof.
destruct n as [| p]; destruct m as [| q]; try reflexivity.
now destruct p.
simpl. rewrite Pminus_mask_succ_r, Pminus_mask_carry_spec.
now destruct (Pminus_mask p q) as [| r |]; [| destruct r |].
Qed.

Theorem NZmul_0_l : forall n : NZ, N0 * n = N0.
Proof.
destruct n; reflexivity.
Qed.

Theorem NZmul_succ_l : forall n m : NZ, (NZsucc n) * m = n * m + m.
Proof.
destruct n as [| n]; destruct m as [| m]; simpl; try reflexivity.
now rewrite Pmult_Sn_m, Pplus_comm.
Qed.

End NZAxiomsMod.

Definition NZlt := Nlt.
Definition NZle := Nle.
Definition NZmin := Nmin.
Definition NZmax := Nmax.

Add Morphism NZlt with signature NZeq ==> NZeq ==> iff as NZlt_wd.
Proof.
unfold NZeq; intros x1 x2 H1 y1 y2 H2; rewrite H1; now rewrite H2.
Qed.

Add Morphism NZle with signature NZeq ==> NZeq ==> iff as NZle_wd.
Proof.
unfold NZeq; intros x1 x2 H1 y1 y2 H2; rewrite H1; now rewrite H2.
Qed.

Add Morphism NZmin with signature NZeq ==> NZeq ==> NZeq as NZmin_wd.
Proof.
congruence.
Qed.

Add Morphism NZmax with signature NZeq ==> NZeq ==> NZeq as NZmax_wd.
Proof.
congruence.
Qed.

Theorem NZlt_eq_cases : forall n m : N, n <= m <-> n < m \/ n = m.
Proof.
intros n m. unfold Nle, Nlt. rewrite <- Ncompare_eq_correct.
destruct (n ?= m); split; intro H1; (try discriminate); try (now left); try now right.
now elim H1. destruct H1; discriminate.
Qed.

Theorem NZlt_irrefl : forall n : NZ, ~ n < n.
Proof.
intro n; unfold Nlt; now rewrite Ncompare_refl.
Qed.

Theorem NZlt_succ_r : forall n m : NZ, n < (NZsucc m) <-> n <= m.
Proof.
intros n m; unfold Nlt, Nle; destruct n as [| p]; destruct m as [| q]; simpl;
split; intro H; try reflexivity; try discriminate.
destruct p; simpl; intros; discriminate. exfalso; now apply H.
apply -> Pcompare_p_Sq in H. destruct H as [H | H].
now rewrite H. now rewrite H, Pcompare_refl.
apply <- Pcompare_p_Sq. case_eq ((p ?= q)%positive Eq); intro H1.
right; now apply Pcompare_Eq_eq. now left. exfalso; now apply H.
Qed.

Theorem NZmin_l : forall n m : N, n <= m -> NZmin n m = n.
Proof.
unfold NZmin, Nmin, Nle; intros n m H.
destruct (n ?= m); try reflexivity. now elim H.
Qed.

Theorem NZmin_r : forall n m : N, m <= n -> NZmin n m = m.
Proof.
unfold NZmin, Nmin, Nle; intros n m H.
case_eq (n ?= m); intro H1; try reflexivity.
now apply -> Ncompare_eq_correct.
rewrite <- Ncompare_antisym, H1 in H; elim H; auto.
Qed.

Theorem NZmax_l : forall n m : N, m <= n -> NZmax n m = n.
Proof.
unfold NZmax, Nmax, Nle; intros n m H.
case_eq (n ?= m); intro H1; try reflexivity.
symmetry; now apply -> Ncompare_eq_correct.
rewrite <- Ncompare_antisym, H1 in H; elim H; auto.
Qed.

Theorem NZmax_r : forall n m : N, n <= m -> NZmax n m = m.
Proof.
unfold NZmax, Nmax, Nle; intros n m H.
destruct (n ?= m); try reflexivity. now elim H.
Qed.

End NZOrdAxiomsMod.

Definition recursion (A : Type) (a : A) (f : N -> A -> A) (n : N) :=
  Nrect (fun _ => A) a f n.
Implicit Arguments recursion [A].

Theorem pred_0 : Npred N0 = N0.
Proof.
reflexivity.
Qed.

Theorem recursion_wd :
forall (A : Type) (Aeq : relation A),
  forall a a' : A, Aeq a a' ->
    forall f f' : N -> A -> A, fun2_eq NZeq Aeq Aeq f f' ->
      forall x x' : N, x = x' ->
        Aeq (recursion a f x) (recursion a' f' x').
Proof.
unfold fun2_wd, NZeq, fun2_eq.
intros A Aeq a a' Eaa' f f' Eff'.
intro x; pattern x; apply Nrect.
intros x' H; now rewrite <- H.
clear x.
intros x IH x' H; rewrite <- H.
unfold recursion in *. do 2 rewrite Nrect_step.
now apply Eff'; [| apply IH].
Qed.

Theorem recursion_0 :
  forall (A : Type) (a : A) (f : N -> A -> A), recursion a f N0 = a.
Proof.
intros A a f; unfold recursion; now rewrite Nrect_base.
Qed.

Theorem recursion_succ :
  forall (A : Type) (Aeq : relation A) (a : A) (f : N -> A -> A),
    Aeq a a -> fun2_wd NZeq Aeq Aeq f ->
      forall n : N, Aeq (recursion a f (Nsucc n)) (f n (recursion a f n)).
Proof.
unfold NZeq, recursion, fun2_wd; intros A Aeq a f EAaa f_wd n; pattern n; apply Nrect.
rewrite Nrect_step; rewrite Nrect_base; now apply f_wd.
clear n; intro n; do 2 rewrite Nrect_step; intro IH. apply f_wd; [reflexivity|].
now rewrite Nrect_step.
Qed.

End NBinaryAxiomsMod.

Module Export NBinarySubPropMod := NSubPropFunct NBinaryAxiomsMod.

(* Some fun comparing the efficiency of the generic log defined
by strong (course-of-value) recursion and the log defined by recursion
on notation *)
(* Time Eval compute in (log 100000). *) (* 98 sec *)

(*
Fixpoint binposlog (p : positive) : N :=
match p with
| xH => 0
| xO p' => Nsucc (binposlog p')
| xI p' => Nsucc (binposlog p')
end.

Definition binlog (n : N) : N :=
match n with
| 0 => 0
| Npos p => binposlog p
end.
*)
(* Eval compute in (binlog 1000000000000000000). *) (* Works very fast *)

