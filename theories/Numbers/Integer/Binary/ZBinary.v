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

Require Import ZMulOrder.
Require Import ZArith.

Open Local Scope Z_scope.

Module ZBinAxiomsMod <: ZAxiomsSig.
Module Export NZOrdAxiomsMod <: NZOrdAxiomsSig.
Module Export NZAxiomsMod <: NZAxiomsSig.

Definition NZ := Z.
Definition NZeq := (@eq Z).
Definition NZ0 := 0.
Definition NZsucc := Zsucc'.
Definition NZpred := Zpred'.
Definition NZadd := Zplus.
Definition NZsub := Zminus.
Definition NZmul := Zmult.

Instance NZeq_equiv : Equivalence NZeq.
Program Instance NZsucc_wd : Proper (eq==>eq) NZsucc.
Program Instance NZpred_wd : Proper (eq==>eq) NZpred.
Program Instance NZadd_wd : Proper (eq==>eq==>eq) NZadd.
Program Instance NZsub_wd : Proper (eq==>eq==>eq) NZsub.
Program Instance NZmul_wd : Proper (eq==>eq==>eq) NZmul.

Theorem NZpred_succ : forall n : Z, NZpred (NZsucc n) = n.
Proof.
exact Zpred'_succ'.
Qed.

Theorem NZinduction :
  forall A : Z -> Prop, Proper (NZeq ==> iff) A ->
    A 0 -> (forall n : Z, A n <-> A (NZsucc n)) -> forall n : Z, A n.
Proof.
intros A A_wd A0 AS n; apply Zind; clear n.
assumption.
intros; now apply -> AS.
intros n H. rewrite <- (Zsucc'_pred' n) in H. now apply <- AS.
Qed.

Theorem NZadd_0_l : forall n : Z, 0 + n = n.
Proof.
exact Zplus_0_l.
Qed.

Theorem NZadd_succ_l : forall n m : Z, (NZsucc n) + m = NZsucc (n + m).
Proof.
intros; do 2 rewrite <- Zsucc_succ'; apply Zplus_succ_l.
Qed.

Theorem NZsub_0_r : forall n : Z, n - 0 = n.
Proof.
exact Zminus_0_r.
Qed.

Theorem NZsub_succ_r : forall n m : Z, n - (NZsucc m) = NZpred (n - m).
Proof.
intros; rewrite <- Zsucc_succ'; rewrite <- Zpred_pred';
apply Zminus_succ_r.
Qed.

Theorem NZmul_0_l : forall n : Z, 0 * n = 0.
Proof.
reflexivity.
Qed.

Theorem NZmul_succ_l : forall n m : Z, (NZsucc n) * m = n * m + m.
Proof.
intros; rewrite <- Zsucc_succ'; apply Zmult_succ_l.
Qed.

End NZAxiomsMod.

Definition NZlt := Zlt.
Definition NZle := Zle.
Definition NZmin := Zmin.
Definition NZmax := Zmax.

Program Instance NZlt_wd : Proper (eq==>eq==>iff) NZlt.
Program Instance NZle_wd : Proper (eq==>eq==>iff) NZle.
Program Instance NZmin_wd : Proper (eq==>eq==>eq) NZmin.
Program Instance NZmax_wd : Proper (eq==>eq==>eq) NZmax.

Theorem NZlt_eq_cases : forall n m : Z, n <= m <-> n < m \/ n = m.
Proof.
intros n m; split. apply Zle_lt_or_eq.
intro H; destruct H as [H | H]. now apply Zlt_le_weak. rewrite H; apply Zle_refl.
Qed.

Theorem NZlt_irrefl : forall n : Z, ~ n < n.
Proof.
exact Zlt_irrefl.
Qed.

Theorem NZlt_succ_r : forall n m : Z, n < (NZsucc m) <-> n <= m.
Proof.
intros; unfold NZsucc; rewrite <- Zsucc_succ'; split;
[apply Zlt_succ_le | apply Zle_lt_succ].
Qed.

Theorem NZmin_l : forall n m : NZ, n <= m -> NZmin n m = n.
Proof.
unfold NZmin, Zmin, Zle; intros n m H.
destruct (n ?= m); try reflexivity. now elim H.
Qed.

Theorem NZmin_r : forall n m : NZ, m <= n -> NZmin n m = m.
Proof.
unfold NZmin, Zmin, Zle; intros n m H.
case_eq (n ?= m); intro H1; try reflexivity.
now apply Zcompare_Eq_eq.
apply <- Zcompare_Gt_Lt_antisym in H1. now elim H.
Qed.

Theorem NZmax_l : forall n m : NZ, m <= n -> NZmax n m = n.
Proof.
unfold NZmax, Zmax, Zle; intros n m H.
case_eq (n ?= m); intro H1; try reflexivity.
apply <- Zcompare_Gt_Lt_antisym in H1. now elim H.
Qed.

Theorem NZmax_r : forall n m : NZ, n <= m -> NZmax n m = m.
Proof.
unfold NZmax, Zmax, Zle; intros n m H.
case_eq (n ?= m); intro H1.
now apply Zcompare_Eq_eq. reflexivity. now elim H.
Qed.

End NZOrdAxiomsMod.

Definition Zopp (x : Z) :=
match x with
| Z0 => Z0
| Zpos x => Zneg x
| Zneg x => Zpos x
end.

Program Instance Zopp_wd : Proper (eq==>eq) Zopp.

Theorem Zsucc_pred : forall n : Z, NZsucc (NZpred n) = n.
Proof.
exact Zsucc'_pred'.
Qed.

Theorem Zopp_0 : - 0 = 0.
Proof.
reflexivity.
Qed.

Theorem Zopp_succ : forall n : Z, - (NZsucc n) = NZpred (- n).
Proof.
intro; rewrite <- Zsucc_succ'; rewrite <- Zpred_pred'. apply Zopp_succ.
Qed.

End ZBinAxiomsMod.

Module Export ZBinMulOrderPropMod := ZMulOrderPropFunct ZBinAxiomsMod.

(** Z forms a ring *)

(*Lemma Zring : ring_theory 0 1 NZadd NZmul NZsub Zopp NZeq.
Proof.
constructor.
exact Zadd_0_l.
exact Zadd_comm.
exact Zadd_assoc.
exact Zmul_1_l.
exact Zmul_comm.
exact Zmul_assoc.
exact Zmul_add_distr_r.
intros; now rewrite Zadd_opp_minus.
exact Zadd_opp_r.
Qed.

Add Ring ZR : Zring.*)



(*
Theorem eq_equiv_e : forall x y : Z, E x y <-> e x y.
Proof.
intros x y; unfold E, e, Zeq_bool; split; intro H.
rewrite H; now rewrite Zcompare_refl.
rewrite eq_true_unfold_pos in H.
assert (H1 : (x ?= y) = Eq).
case_eq (x ?= y); intro H1; rewrite H1 in H; simpl in H;
[reflexivity | discriminate H | discriminate H].
now apply Zcompare_Eq_eq.
Qed.
*)
