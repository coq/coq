(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)


Require Import ZAxioms ZProperties.
Require Import BinInt Zcompare Zorder ZArith_dec Zbool.

Local Open Scope Z_scope.

Theorem Z_bi_induction :
  forall A : Z -> Prop, Proper (eq ==> iff) A ->
    A 0 -> (forall n : Z, A n <-> A (Zsucc n)) -> forall n : Z, A n.
Proof.
intros A A_wd A0 AS n; apply Zind; clear n.
assumption.
intros; rewrite <- Zsucc_succ'. now apply -> AS.
intros n H. rewrite <- Zpred_pred'. rewrite Zsucc_pred in H. now apply <- AS.
Qed.


(** * Implementation of [ZAxiomsSig] by [BinInt.Z] *)

Module Z
 <: ZAxiomsExtSig <: UsualOrderedTypeFull <: TotalOrder
 <: UsualDecidableTypeFull.

Definition t := Z.
Definition eqb := Zeq_bool.
Definition zero := 0.
Definition succ := Zsucc.
Definition pred := Zpred.
Definition add := Zplus.
Definition sub := Zminus.
Definition mul := Zmult.
Definition lt := Zlt.
Definition le := Zle.
Definition compare := Zcompare.
Definition min := Zmin.
Definition max := Zmax.
Definition opp := Zopp.
Definition abs := Zabs.
Definition sgn := Zsgn.

Definition eq_dec := Z_eq_dec.

Definition bi_induction := Z_bi_induction.

(** Basic operations. *)

Definition eq_equiv : Equivalence (@eq Z) := eq_equivalence.
Local Obligation Tactic := simpl_relation.
Program Instance succ_wd : Proper (eq==>eq) Zsucc.
Program Instance pred_wd : Proper (eq==>eq) Zpred.
Program Instance add_wd : Proper (eq==>eq==>eq) Zplus.
Program Instance sub_wd : Proper (eq==>eq==>eq) Zminus.
Program Instance mul_wd : Proper (eq==>eq==>eq) Zmult.

Definition pred_succ n := eq_sym (Zpred_succ n).
Definition add_0_l := Zplus_0_l.
Definition add_succ_l := Zplus_succ_l.
Definition sub_0_r := Zminus_0_r.
Definition sub_succ_r := Zminus_succ_r.
Definition mul_0_l := Zmult_0_l.
Definition mul_succ_l := Zmult_succ_l.

(** Boolean Equality *)

Definition eqb_eq x y := iff_sym (Zeq_is_eq_bool x y).

(** Order *)

Program Instance lt_wd : Proper (eq==>eq==>iff) Zlt.

Definition lt_eq_cases := Zle_lt_or_eq_iff.
Definition lt_irrefl := Zlt_irrefl.
Definition lt_succ_r := Zlt_succ_r.

(** Comparison *)

Definition compare_spec := Zcompare_spec.

(** Minimum and maximum *)

Definition min_l := Zmin_l.
Definition min_r := Zmin_r.
Definition max_l := Zmax_l.
Definition max_r := Zmax_r.

(** Properties specific to integers, not natural numbers. *)

Program Instance opp_wd : Proper (eq==>eq) Zopp.

Definition succ_pred n := eq_sym (Zsucc_pred n).
Definition opp_0 := Zopp_0.
Definition opp_succ := Zopp_succ.

(** Absolute value and sign *)

Definition abs_eq := Zabs_eq.
Definition abs_neq := Zabs_non_eq.

Definition sgn_null := Zsgn_0.
Definition sgn_pos := Zsgn_1.
Definition sgn_neg := Zsgn_m1.

(** We define [eq] only here to avoid refering to this [eq] above. *)

Definition eq := (@eq Z).

(** Now the generic properties. *)

Include ZPropFunct
 <+ UsualMinMaxLogicalProperties <+ UsualMinMaxDecProperties.

End Z.

(** * An [order] tactic for integers *)

Ltac z_order := Z.order.

(** Note that [z_order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)

Section TestOrder.
 Let test : forall x y, x<=y -> y<=x -> x=y.
 Proof.
 z_order.
 Qed.
End TestOrder.

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
