(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import BinInt.
Require Import Zcompare.
Require Import Zorder.
Require Import Znat.
Require Import Zmisc.
Require Import Wf_nat.
Local Open Scope Z_scope.

(** Our purpose is to write an induction shema for {0,1,2,...}
  similar to the [nat] schema (Theorem [Natlike_rec]). For that the
  following implications will be used :
<<
 ∀n:nat, Q n == ∀n:nat, P (Z.of_nat n) ===> ∀x:Z, x <= 0 -> P x

       	     /\
             ||
             ||

 (Q O) ∧ (∀n:nat, Q n -> Q (S n)) <=== (P 0) ∧ (∀x:Z, P x -> P (Z.succ x))

				  <=== (Z.of_nat (S n) = Z.succ (Z.of_nat n))

				  <=== Z_of_nat_complete
>>
  Then the  diagram will be closed and the theorem proved. *)

Lemma Z_of_nat_complete (x : Z) :
 0 <= x -> exists n : nat, x = Z.of_nat n.
Proof.
 intros H. exists (Z.to_nat x). symmetry. now apply Z2Nat.id.
Qed.

Lemma Z_of_nat_complete_inf (x : Z) :
 0 <= x -> {n : nat | x = Z.of_nat n}.
Proof.
 intros H. exists (Z.to_nat x). symmetry. now apply Z2Nat.id.
Qed.

Lemma Z_of_nat_prop :
  forall P:Z -> Prop,
    (forall n:nat, P (Z.of_nat n)) -> forall x:Z, 0 <= x -> P x.
Proof.
 intros P H x Hx. now destruct (Z_of_nat_complete x Hx) as (n,->).
Qed.

Lemma Z_of_nat_set :
 forall P:Z -> Set,
   (forall n:nat, P (Z.of_nat n)) -> forall x:Z, 0 <= x -> P x.
Proof.
 intros P H x Hx. now destruct (Z_of_nat_complete_inf x Hx) as (n,->).
Qed.

Lemma natlike_ind :
 forall P:Z -> Prop,
   P 0 ->
   (forall x:Z, 0 <= x -> P x -> P (Z.succ x)) ->
   forall x:Z, 0 <= x -> P x.
Proof.
 intros P Ho Hrec x Hx; apply Z_of_nat_prop; trivial.
 induction n. exact Ho.
 rewrite Nat2Z.inj_succ. apply Hrec; trivial using Nat2Z.is_nonneg.
Qed.

Lemma natlike_rec :
 forall P:Z -> Set,
   P 0 ->
   (forall x:Z, 0 <= x -> P x -> P (Z.succ x)) ->
   forall x:Z, 0 <= x -> P x.
Proof.
 intros P Ho Hrec x Hx; apply Z_of_nat_set; trivial.
 induction n. exact Ho.
 rewrite Nat2Z.inj_succ. apply Hrec; trivial using Nat2Z.is_nonneg.
Qed.

Section Efficient_Rec.

  (** [natlike_rec2] is the same as [natlike_rec], but with a different proof, designed
      to give a better extracted term. *)

  Let R (a b:Z) := 0 <= a /\ a < b.

  Let R_wf : well_founded R.
  Proof.
   apply well_founded_lt_compat with Z.to_nat.
   intros x y (Hx,H). apply Z2Nat.inj_lt; Z.order.
  Qed.

  Lemma natlike_rec2 :
    forall P:Z -> Type,
      P 0 ->
      (forall z:Z, 0 <= z -> P z -> P (Z.succ z)) ->
      forall z:Z, 0 <= z -> P z.
  Proof.
   intros P Ho Hrec.
   induction z as [z IH] using (well_founded_induction_type R_wf).
   destruct z; intros Hz.
   - apply Ho.
   - set (y:=Z.pred (Zpos p)).
     assert (LE : 0 <= y) by (unfold y; now apply Z.lt_le_pred).
     assert (EQ : Zpos p = Z.succ y) by (unfold y; now rewrite Z.succ_pred).
     rewrite EQ. apply Hrec, IH; trivial.
     split; trivial. unfold y; apply Z.lt_pred_l.
   - now destruct Hz.
  Qed.

  (** A variant of the previous using [Z.pred] instead of [Z.succ]. *)

  Lemma natlike_rec3 :
    forall P:Z -> Type,
      P 0 ->
      (forall z:Z, 0 < z -> P (Z.pred z) -> P z) ->
      forall z:Z, 0 <= z -> P z.
  Proof.
   intros P Ho Hrec.
   induction z as [z IH] using (well_founded_induction_type R_wf).
   destruct z; intros Hz.
   - apply Ho.
   - assert (EQ : 0 <= Z.pred (Zpos p)) by now apply Z.lt_le_pred.
     apply Hrec. easy. apply IH; trivial. split; trivial.
     apply Z.lt_pred_l.
   - now destruct Hz.
  Qed.

  (** A more general induction principle on non-negative numbers using [Z.lt]. *)

  Lemma Zlt_0_rec :
    forall P:Z -> Type,
      (forall x:Z, (forall y:Z, 0 <= y < x -> P y) -> 0 <= x -> P x) ->
      forall x:Z, 0 <= x -> P x.
  Proof.
   intros P Hrec.
   induction x as [x IH] using (well_founded_induction_type R_wf).
   destruct x; intros Hx.
   - apply Hrec; trivial. intros y (Hy,Hy').
     assert (0 < 0) by now apply Z.le_lt_trans with y.
     discriminate.
   - apply Hrec; trivial. intros y (Hy,Hy').
     apply IH; trivial. now split.
   - now destruct Hx.
  Defined.

  Lemma Zlt_0_ind :
    forall P:Z -> Prop,
      (forall x:Z, (forall y:Z, 0 <= y < x -> P y) -> 0 <= x -> P x) ->
      forall x:Z, 0 <= x -> P x.
  Proof. intros; now apply Zlt_0_rec. Qed.

  (** Obsolete version of [Z.lt] induction principle on non-negative numbers *)

  Lemma Z_lt_rec :
    forall P:Z -> Type,
      (forall x:Z, (forall y:Z, 0 <= y < x -> P y) -> P x) ->
      forall x:Z, 0 <= x -> P x.
  Proof.
    intros P Hrec; apply Zlt_0_rec; auto.
  Qed.

  Lemma Z_lt_induction :
    forall P:Z -> Prop,
      (forall x:Z, (forall y:Z, 0 <= y < x -> P y) -> P x) ->
      forall x:Z, 0 <= x -> P x.
  Proof.
    intros; now apply Z_lt_rec.
  Qed.

  (** An even more general induction principle using [Z.lt]. *)

  Lemma Zlt_lower_bound_rec :
    forall P:Z -> Type, forall z:Z,
      (forall x:Z, (forall y:Z, z <= y < x -> P y) -> z <= x -> P x) ->
      forall x:Z, z <= x -> P x.
  Proof.
    intros P z Hrec x Hx.
    rewrite <- (Z.sub_simpl_r x z). apply Z.le_0_sub in Hx.
    pattern (x - z); apply Zlt_0_rec; trivial.
    clear x Hx. intros x IH Hx.
    apply Hrec. intros y (Hy,Hy').
    rewrite <- (Z.sub_simpl_r y z). apply IH; split.
    now rewrite Z.le_0_sub.
    now apply Z.lt_sub_lt_add_r.
    now rewrite <- (Z.add_le_mono_r 0 x z).
  Qed.

  Lemma Zlt_lower_bound_ind :
    forall P:Z -> Prop, forall z:Z,
      (forall x:Z, (forall y:Z, z <= y < x -> P y) -> z <= x -> P x) ->
      forall x:Z, z <= x -> P x.
  Proof.
    intros; now apply Zlt_lower_bound_rec with z.
  Qed.

End Efficient_Rec.
