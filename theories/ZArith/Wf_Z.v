(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import BinInt.
Require Import Zcompare.
Require Import Zorder.
Require Import Znat.
Require Import Zmisc.
Require Import Wf_nat.
Open Local Scope Z_scope.

(** Our purpose is to write an induction shema for {0,1,2,...}
  similar to the [nat] schema (Theorem [Natlike_rec]). For that the
  following implications will be used :
<<
 (n:nat)(Q n)==(n:nat)(P (inject_nat n)) ===> (x:Z)`x > 0) -> (P x)

       	     /\
             ||
             ||

  (Q O) (n:nat)(Q n)->(Q (S n)) <=== (P 0) (x:Z) (P x) -> (P (Zs x))

      	       	       	       	<=== (inject_nat (S n))=(Zs (inject_nat n))

      	       	       	       	<=== inject_nat_complete
>>
  Then the  diagram will be closed and the theorem proved. *)

Lemma Z_of_nat_complete :
  forall x:Z, 0 <= x ->  exists n : nat, x = Z_of_nat n.
Proof.
  intro x; destruct x; intros;
    [ exists 0%nat; auto with arith
      | specialize (ZL4 p); intros Hp; elim Hp; intros; exists (S x); intros;
	simpl in |- *; specialize (nat_of_P_o_P_of_succ_nat_eq_succ x);
	  intro Hx0; rewrite <- H0 in Hx0; apply f_equal with (f := Zpos);
	    apply nat_of_P_inj; auto with arith
      | absurd (0 <= Zneg p);
	[ unfold Zle in |- *; simpl in |- *; do 2 unfold not in |- *;
	  auto with arith
	  | assumption ] ].
Qed.

Lemma ZL4_inf : forall y:positive, {h : nat | nat_of_P y = S h}.
Proof.
  intro y; induction y as [p H| p H1| ];
    [ elim H; intros x H1; exists (S x + S x)%nat; unfold nat_of_P in |- *;
      simpl in |- *; rewrite ZL0; rewrite Pmult_nat_r_plus_morphism;
	unfold nat_of_P in H1; rewrite H1; auto with arith
      | elim H1; intros x H2; exists (x + S x)%nat; unfold nat_of_P in |- *;
	simpl in |- *; rewrite ZL0; rewrite Pmult_nat_r_plus_morphism;
	  unfold nat_of_P in H2; rewrite H2; auto with arith
      | exists 0%nat; auto with arith ].
Qed.

Lemma Z_of_nat_complete_inf :
 forall x:Z, 0 <= x -> {n : nat | x = Z_of_nat n}.
Proof.
  intro x; destruct x; intros;
    [ exists 0%nat; auto with arith
      | specialize (ZL4_inf p); intros Hp; elim Hp; intros x0 H0; exists (S x0);
	intros; simpl in |- *; specialize (nat_of_P_o_P_of_succ_nat_eq_succ x0);
	  intro Hx0; rewrite <- H0 in Hx0; apply f_equal with (f := Zpos);
	    apply nat_of_P_inj; auto with arith
      | absurd (0 <= Zneg p);
	[ unfold Zle in |- *; simpl in |- *; do 2 unfold not in |- *;
	  auto with arith
	  | assumption ] ].
Qed.

Lemma Z_of_nat_prop :
  forall P:Z -> Prop,
    (forall n:nat, P (Z_of_nat n)) -> forall x:Z, 0 <= x -> P x.
Proof.
  intros P H x H0.
  specialize (Z_of_nat_complete x H0).
  intros Hn; elim Hn; intros.
  rewrite H1; apply H.
Qed.

Lemma Z_of_nat_set :
 forall P:Z -> Set,
   (forall n:nat, P (Z_of_nat n)) -> forall x:Z, 0 <= x -> P x.
Proof.
  intros P H x H0.
  specialize (Z_of_nat_complete_inf x H0).
  intros Hn; elim Hn; intros.
  rewrite p; apply H.
Qed.

Lemma natlike_ind :
 forall P:Z -> Prop,
   P 0 ->
   (forall x:Z, 0 <= x -> P x -> P (Zsucc x)) -> forall x:Z, 0 <= x -> P x.
Proof.
  intros P H H0 x H1; apply Z_of_nat_prop;
    [ simple induction n;
      [ simpl in |- *; assumption
	| intros; rewrite (inj_S n0); exact (H0 (Z_of_nat n0) (Zle_0_nat n0) H2) ]
      | assumption ].
Qed.

Lemma natlike_rec :
 forall P:Z -> Set,
   P 0 ->
   (forall x:Z, 0 <= x -> P x -> P (Zsucc x)) -> forall x:Z, 0 <= x -> P x.
Proof.
  intros P H H0 x H1; apply Z_of_nat_set;
    [ simple induction n;
      [ simpl in |- *; assumption
	| intros; rewrite (inj_S n0); exact (H0 (Z_of_nat n0) (Zle_0_nat n0) H2) ]
      | assumption ].
Qed.

Section Efficient_Rec.

  (** [natlike_rec2] is the same as [natlike_rec], but with a different proof, designed
      to give a better extracted term. *)

  Let R (a b:Z) := 0 <= a /\ a < b.

  Let R_wf : well_founded R.
  Proof.
    set
      (f :=
	fun z =>
	  match z with
	    | Zpos p => nat_of_P p
	    | Z0 => 0%nat
	    | Zneg _ => 0%nat
	  end) in *.
    apply well_founded_lt_compat with f.
    unfold R, f in |- *; clear f R.
    intros x y; case x; intros; elim H; clear H.
    case y; intros; apply lt_O_nat_of_P || inversion H0.
    case y; intros; apply nat_of_P_lt_Lt_compare_morphism || inversion H0; auto.
    intros; elim H; auto.
  Qed.

  Lemma natlike_rec2 :
    forall P:Z -> Type,
      P 0 ->
      (forall z:Z, 0 <= z -> P z -> P (Zsucc z)) -> forall z:Z, 0 <= z -> P z.
  Proof.
    intros P Ho Hrec z; pattern z in |- *;
      apply (well_founded_induction_type R_wf).
    intro x; case x.
    trivial.
    intros.
    assert (0 <= Zpred (Zpos p)).
    apply Zorder.Zlt_0_le_0_pred; unfold Zlt in |- *; simpl in |- *; trivial.
    rewrite Zsucc_pred.
    apply Hrec.
    auto.
    apply X; auto; unfold R in |- *; intuition; apply Zlt_pred.
    intros; elim H; simpl in |- *; trivial.
  Qed.

  (** A variant of the previous using [Zpred] instead of [Zs]. *)

  Lemma natlike_rec3 :
    forall P:Z -> Type,
      P 0 ->
      (forall z:Z, 0 < z -> P (Zpred z) -> P z) -> forall z:Z, 0 <= z -> P z.
  Proof.
    intros P Ho Hrec z; pattern z in |- *;
      apply (well_founded_induction_type R_wf).
    intro x; case x.
    trivial.
    intros; apply Hrec.
    unfold Zlt in |- *; trivial.
    assert (0 <= Zpred (Zpos p)).
    apply Zorder.Zlt_0_le_0_pred; unfold Zlt in |- *; simpl in |- *; trivial.
    apply X; auto; unfold R in |- *; intuition; apply Zlt_pred.
    intros; elim H; simpl in |- *; trivial.
  Qed.

  (** A more general induction principle on non-negative numbers using [Zlt]. *)

  Lemma Zlt_0_rec :
    forall P:Z -> Type,
      (forall x:Z, (forall y:Z, 0 <= y < x -> P y) -> 0 <= x -> P x) ->
      forall x:Z, 0 <= x -> P x.
  Proof.
    intros P Hrec z; pattern z in |- *; apply (well_founded_induction_type R_wf).
    intro x; case x; intros.
    apply Hrec; intros.
    assert (H2 : 0 < 0).
    apply Zle_lt_trans with y; intuition.
    inversion H2.
    assumption.
    firstorder.
    unfold Zle, Zcompare in H; elim H; auto.
  Defined.

  Lemma Zlt_0_ind :
    forall P:Z -> Prop,
      (forall x:Z, (forall y:Z, 0 <= y < x -> P y) -> 0 <= x -> P x) ->
      forall x:Z, 0 <= x -> P x.
  Proof.
    exact Zlt_0_rec.
  Qed.

  (** Obsolete version of [Zlt] induction principle on non-negative numbers *)

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
    exact Z_lt_rec.
  Qed.

  (** An even more general induction principle using [Zlt]. *)

  Lemma Zlt_lower_bound_rec :
    forall P:Z -> Type, forall z:Z,
      (forall x:Z, (forall y:Z, z <= y < x -> P y) -> z <= x -> P x) ->
      forall x:Z, z <= x -> P x.
  Proof.
    intros P z Hrec x.
    assert (Hexpand : forall x, x = x - z + z).
    intro; unfold Zminus; rewrite <- Zplus_assoc; rewrite Zplus_opp_l;
      rewrite Zplus_0_r; trivial.
    intro Hz.
    rewrite (Hexpand x); pattern (x - z) in |- *; apply Zlt_0_rec.
    2: apply Zplus_le_reg_r with z; rewrite <- Hexpand; assumption.
    intros x0 Hlt_x0 H.
    apply Hrec.
    2: change z with (0+z); apply Zplus_le_compat_r; assumption.
    intro y; rewrite (Hexpand y); intros.
    destruct H0.
    apply Hlt_x0.
    split.
    apply Zplus_le_reg_r with z; assumption.
    apply Zplus_lt_reg_r with z; assumption.
  Qed.

  Lemma Zlt_lower_bound_ind :
    forall P:Z -> Prop, forall z:Z,
      (forall x:Z, (forall y:Z, z <= y < x -> P y) -> z <= x -> P x) ->
      forall x:Z, z <= x -> P x.
  Proof.
    exact Zlt_lower_bound_rec.
  Qed.

End Efficient_Rec.
