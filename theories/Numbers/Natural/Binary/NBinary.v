(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Import BinPos Ndiv_def Nsqrt_def Ngcd_def Ndigits.
Require Export BinNat.
Require Import NAxioms NProperties.

Local Open Scope N_scope.

(** * Implementation of [NAxiomsSig] module type via [BinNat.N] *)

Module Type N
 <: NAxiomsMiniSig <: UsualOrderedTypeFull <: TotalOrder <: DecidableTypeFull.

(** Bi-directional induction. *)

Theorem bi_induction :
  forall A : N -> Prop, Proper (eq==>iff) A ->
    A N0 -> (forall n, A n <-> A (Nsucc n)) -> forall n : N, A n.
Proof.
intros A A_wd A0 AS. apply Nrect. assumption. intros; now apply -> AS.
Qed.

(** Basic operations. *)

Definition eq_equiv : Equivalence (@eq N) := eq_equivalence.
Local Obligation Tactic := simpl_relation.
Program Instance succ_wd : Proper (eq==>eq) Nsucc.
Program Instance pred_wd : Proper (eq==>eq) Npred.
Program Instance add_wd : Proper (eq==>eq==>eq) Nplus.
Program Instance sub_wd : Proper (eq==>eq==>eq) Nminus.
Program Instance mul_wd : Proper (eq==>eq==>eq) Nmult.

Definition pred_succ := Npred_succ.
Definition add_0_l := Nplus_0_l.
Definition add_succ_l := Nplus_succ.
Definition sub_0_r := Nminus_0_r.
Definition sub_succ_r := Nminus_succ_r.
Definition mul_0_l := Nmult_0_l.
Definition mul_succ_l n m := eq_trans (Nmult_Sn_m n m) (Nplus_comm _ _).

Lemma one_succ : 1 = Nsucc 0.
Proof.
reflexivity.
Qed.

Lemma two_succ : 2 = Nsucc 1.
Proof.
reflexivity.
Qed.

(** Order *)

Program Instance lt_wd : Proper (eq==>eq==>iff) Nlt.

Definition lt_eq_cases := Nle_lteq.
Definition lt_irrefl := Nlt_irrefl.
Definition lt_succ_r := Nlt_succ_r.
Definition eqb_eq := Neqb_eq.

Definition compare_spec := Ncompare_spec.

Theorem min_l : forall n m, n <= m -> Nmin n m = n.
Proof.
unfold Nmin, Nle; intros n m H.
destruct (n ?= m); try reflexivity. now elim H.
Qed.

Theorem min_r : forall n m, m <= n -> Nmin n m = m.
Proof.
unfold Nmin, Nle; intros n m H.
case_eq (n ?= m); intro H1; try reflexivity.
now apply Ncompare_eq_correct.
rewrite <- Ncompare_antisym, H1 in H; elim H; auto.
Qed.

Theorem max_l : forall n m, m <= n -> Nmax n m = n.
Proof.
unfold Nmax, Nle; intros n m H.
case_eq (n ?= m); intro H1; try reflexivity.
symmetry; now apply Ncompare_eq_correct.
rewrite <- Ncompare_antisym, H1 in H; elim H; auto.
Qed.

Theorem max_r : forall n m : N, n <= m -> Nmax n m = m.
Proof.
unfold Nmax, Nle; intros n m H.
destruct (n ?= m); try reflexivity. now elim H.
Qed.

(** Part specific to natural numbers, not integers. *)

Theorem pred_0 : Npred 0 = 0.
Proof.
reflexivity.
Qed.

Definition recursion (A : Type) : A -> (N -> A -> A) -> N -> A :=
  Nrect (fun _ => A).
Implicit Arguments recursion [A].

Instance recursion_wd A (Aeq : relation A) :
 Proper (Aeq==>(eq==>Aeq==>Aeq)==>eq==>Aeq) (@recursion A).
Proof.
intros a a' Eaa' f f' Eff'.
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
    Aeq a a -> Proper (eq==>Aeq==>Aeq) f ->
      forall n : N, Aeq (recursion a f (Nsucc n)) (f n (recursion a f n)).
Proof.
unfold recursion; intros A Aeq a f EAaa f_wd n; pattern n; apply Nrect.
rewrite Nrect_step; rewrite Nrect_base; now apply f_wd.
clear n; intro n; do 2 rewrite Nrect_step; intro IH. apply f_wd; [reflexivity|].
now rewrite Nrect_step.
Qed.

(** Division and modulo *)

Program Instance div_wd : Proper (eq==>eq==>eq) Ndiv.
Program Instance mod_wd : Proper (eq==>eq==>eq) Nmod.

Definition div_mod := fun x y (_:y<>0) => Ndiv_mod_eq x y.
Definition mod_bound_pos : forall a b, 0<=a -> 0<b -> 0<= a mod b < b.
Proof. split. now destruct (a mod b). apply Nmod_lt. now destruct b. Qed.

(** Odd and Even *)

Definition Even n := exists m, n = 2*m.
Definition Odd n := exists m, n = 2*m+1.
Definition even_spec := Neven_spec.
Definition odd_spec := Nodd_spec.

(** Power *)

Program Instance pow_wd : Proper (eq==>eq==>eq) Npow.
Definition pow_0_r := Npow_0_r.
Definition pow_succ_r n p (H:0 <= p) := Npow_succ_r n p.
Lemma pow_neg_r : forall a b, b<0 -> a^b = 0.
Proof. destruct b; discriminate. Qed.

(** Log2 *)

Definition log2_spec := Nlog2_spec.
Definition log2_nonpos := Nlog2_nonpos.

(** Sqrt *)

Definition sqrt_spec n (H:0<=n) := Nsqrt_spec n.
Lemma sqrt_neg : forall a, a<0 -> Nsqrt a = 0.
Proof. destruct a; discriminate. Qed.

(** Gcd *)

Definition gcd_divide_l := Ngcd_divide_l.
Definition gcd_divide_r := Ngcd_divide_r.
Definition gcd_greatest := Ngcd_greatest.
Lemma gcd_nonneg : forall a b, 0 <= Ngcd a b.
Proof. intros. now destruct (Ngcd a b). Qed.

(** Bitwise Operations *)

Program Instance testbit_wd : Proper (eq==>eq==>Logic.eq) Ntestbit.
Definition testbit_odd_0 := Ntestbit_odd_0.
Definition testbit_even_0 := Ntestbit_even_0.
Definition testbit_odd_succ a n (_:0<=n) := Ntestbit_odd_succ a n.
Definition testbit_even_succ a n (_:0<=n) := Ntestbit_even_succ a n.
Lemma testbit_neg_r a n (H:n<0) : Ntestbit a n = false.
Proof. now destruct n. Qed.
Definition shiftl_spec_low := Nshiftl_spec_low.
Definition shiftl_spec_high a n m (_:0<=m) := Nshiftl_spec_high a n m.
Definition shiftr_spec a n m (_:0<=m) := Nshiftr_spec a n m.
Definition lxor_spec := Nxor_spec.
Definition land_spec := Nand_spec.
Definition lor_spec := Nor_spec.
Definition ldiff_spec := Ndiff_spec.
Definition div2_spec a : Ndiv2 a = Nshiftr a 1 := eq_refl _.

(** The instantiation of operations.
    Placing them at the very end avoids having indirections in above lemmas. *)

Definition t := N.
Definition eq := @eq N.
Definition eqb := Neqb.
Definition compare := Ncompare.
Definition eq_dec := N_eq_dec.
Definition zero := 0.
Definition one := 1.
Definition two := 2.
Definition succ := Nsucc.
Definition pred := Npred.
Definition add := Nplus.
Definition sub := Nminus.
Definition mul := Nmult.
Definition lt := Nlt.
Definition le := Nle.
Definition min := Nmin.
Definition max := Nmax.
Definition div := Ndiv.
Definition modulo := Nmod.
Definition pow := Npow.
Definition even := Neven.
Definition odd := Nodd.
Definition sqrt := Nsqrt.
Definition log2 := Nlog2.
Definition divide := Ndivide.
Definition gcd := Ngcd.
Definition testbit := Ntestbit.
Definition shiftl := Nshiftl.
Definition shiftr := Nshiftr.
Definition lxor := Nxor.
Definition land := Nand.
Definition lor := Nor.
Definition ldiff := Ndiff.
Definition div2 := Ndiv2.

Include NProp [scope abstract_scope to N_scope]
 <+ UsualMinMaxLogicalProperties [scope abstract_scope to N_scope]
 <+ UsualMinMaxDecProperties [scope abstract_scope to N_scope].

End N.

(*
Require Import NDefOps.
Module Import NBinaryDefOpsMod := NdefOpsPropFunct NBinaryAxiomsMod.

(* Some fun comparing the efficiency of the generic log defined
by strong (course-of-value) recursion and the log defined by recursion
on notation *)

Time Eval vm_compute in (log 500000). (* 11 sec *)

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

Time Eval vm_compute in (binlog 500000). (* 0 sec *)
Time Eval vm_compute in (binlog 1000000000000000000000000000000). (* 0 sec *)

*)
