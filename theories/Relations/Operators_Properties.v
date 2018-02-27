(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(** * Some properties of the operators on relations                     *)
(************************************************************************)
(** * Initial version by Bruno Barras                                   *)
(************************************************************************)

Require Import Relation_Definitions.
Require Import Relation_Operators.

Section Properties.

  Arguments clos_refl [A] R x _.
  Arguments clos_refl_trans [A] R x _.
  Arguments clos_refl_trans_1n [A] R x _.
  Arguments clos_refl_trans_n1 [A] R x _.
  Arguments clos_refl_sym_trans [A] R _ _.
  Arguments clos_refl_sym_trans_1n [A] R x _.
  Arguments clos_refl_sym_trans_n1 [A] R x _.
  Arguments clos_trans [A] R x _.
  Arguments clos_trans_1n [A] R x _.
  Arguments clos_trans_n1 [A] R x _.
  Arguments inclusion [A] R1 R2.
  Arguments preorder [A] R.

  Variable A : Type.
  Variable R : relation A.

  Section Clos_Refl_Trans.

    Local Notation "R *" := (clos_refl_trans R)
      (at level 8, no associativity, format "R *").

    (** Correctness of the reflexive-transitive closure operator *)

    Lemma clos_rt_is_preorder : preorder R*.
    Proof.
      apply Build_preorder.
      exact (rt_refl A R).

      exact (rt_trans A R).
    Qed.

    (** Idempotency of the reflexive-transitive closure operator *)

    Lemma clos_rt_idempotent : inclusion (R*)* R*.
    Proof.
      red.
      induction 1; auto with sets.
      intros.
      apply rt_trans with y; auto with sets.
    Qed.

  End Clos_Refl_Trans.

  Section Clos_Refl_Sym_Trans.

    (** Reflexive-transitive closure is included in the
        reflexive-symmetric-transitive closure *)

    Lemma clos_rt_clos_rst :
      inclusion (clos_refl_trans R) (clos_refl_sym_trans R).
    Proof.
      red.
      induction 1; auto with sets.
      apply rst_trans with y; auto with sets.
    Qed.

    (** Reflexive closure is included in the
        reflexive-transitive closure *)

    Lemma clos_r_clos_rt :
      inclusion (clos_refl R) (clos_refl_trans R).
    Proof.
      induction 1 as [? ?| ].
      constructor; auto.
      constructor 2.
    Qed.

    Lemma clos_rt_t : forall x y z,
      clos_refl_trans R x y -> clos_trans R y z ->
      clos_trans R x z.
    Proof.
      induction 1 as [b d H1|b|a b d H1 H2 IH1 IH2]; auto.
      intro H. apply t_trans with (y:=d); auto.
      constructor. auto.
    Qed.

    (** Correctness of the reflexive-symmetric-transitive closure *)

    Lemma clos_rst_is_equiv : equivalence A (clos_refl_sym_trans R).
    Proof.
      apply Build_equivalence.
      exact (rst_refl A R).
      exact (rst_trans A R).
      exact (rst_sym A R).
    Qed.

    (** Idempotency of the reflexive-symmetric-transitive closure operator *)

    Lemma clos_rst_idempotent :
      inclusion (clos_refl_sym_trans (clos_refl_sym_trans R))
      (clos_refl_sym_trans R).
    Proof.
      red.
      induction 1; auto with sets.
      apply rst_trans with y; auto with sets.
    Qed.

  End Clos_Refl_Sym_Trans.

  Section Equivalences.

  (** *** Equivalences between the different definition of the reflexive,
      symmetric, transitive closures *)

  (** *** Contributed by P. Castéran *)

    (** Direct transitive closure vs left-step extension *)

    Lemma clos_t1n_trans : forall x y, clos_trans_1n R x y -> clos_trans R x y.
    Proof.
     induction 1.
     left; assumption.
     right with y; auto.
     left; auto.
    Qed.

    Lemma clos_trans_t1n : forall x y, clos_trans R x y -> clos_trans_1n R x y.
    Proof.
      induction 1.
      left; assumption.
      generalize IHclos_trans2; clear IHclos_trans2; induction IHclos_trans1.
      right with y; auto.
      right with y; auto.
      eapply IHIHclos_trans1; auto.
      apply clos_t1n_trans; auto.
    Qed.

    Lemma clos_trans_t1n_iff : forall x y,
        clos_trans R x y <-> clos_trans_1n R x y.
    Proof.
      split.
      apply clos_trans_t1n.
      apply clos_t1n_trans.
    Qed.

    (** Direct transitive closure vs right-step extension *)

    Lemma clos_tn1_trans : forall x y, clos_trans_n1 R x y -> clos_trans R x y.
    Proof.
      induction 1.
      left; assumption.
      right with y; auto.
      left; assumption.
    Qed.

    Lemma clos_trans_tn1 :  forall x y, clos_trans R x y -> clos_trans_n1 R x y.
    Proof.
      induction 1.
      left; assumption.
      elim IHclos_trans2.
      intro y0; right with y.
      auto.
      auto.
      intros.
      right with y0; auto.
    Qed.

    Lemma clos_trans_tn1_iff : forall x y,
        clos_trans R x y <-> clos_trans_n1 R x y.
    Proof.
      split.
      apply clos_trans_tn1.
      apply clos_tn1_trans.
    Qed.

    (** Direct reflexive-transitive closure is equivalent to
        transitivity by left-step extension *)

    Lemma clos_rt1n_step : forall x y, R x y -> clos_refl_trans_1n R x y.
    Proof.
      intros x y H.
      right with y;[assumption|left].
    Qed.

    Lemma clos_rtn1_step : forall x y, R x y -> clos_refl_trans_n1 R x y.
    Proof.
      intros x y H.
      right with x;[assumption|left].
    Qed.

    Lemma clos_rt1n_rt : forall x y,
        clos_refl_trans_1n R x y -> clos_refl_trans R x y.
    Proof.
      induction 1.
      constructor 2.
      constructor 3 with y; auto.
      constructor 1; auto.
    Qed.

    Lemma clos_rt_rt1n : forall x y,
        clos_refl_trans R x y -> clos_refl_trans_1n R x y.
    Proof.
      induction 1.
      apply clos_rt1n_step; assumption.
      left.
      generalize IHclos_refl_trans2; clear IHclos_refl_trans2;
        induction IHclos_refl_trans1; auto.

      right with y; auto.
      eapply IHIHclos_refl_trans1; auto.
      apply clos_rt1n_rt; auto.
    Qed.

    Lemma clos_rt_rt1n_iff : forall x y,
      clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
    Proof.
      split.
      apply clos_rt_rt1n.
      apply clos_rt1n_rt.
    Qed.

    (** Direct reflexive-transitive closure is equivalent to
        transitivity by right-step extension *)

    Lemma clos_rtn1_rt : forall x y,
        clos_refl_trans_n1 R x y -> clos_refl_trans R x y.
    Proof.
      induction 1.
      constructor 2.
      constructor 3 with y; auto.
      constructor 1; assumption.
    Qed.

    Lemma clos_rt_rtn1 :  forall x y,
        clos_refl_trans R x y -> clos_refl_trans_n1 R x y.
    Proof.
      induction 1.
      apply clos_rtn1_step; auto.
      left.
      elim IHclos_refl_trans2; auto.
      intros.
      right with y0; auto.
    Qed.

    Lemma clos_rt_rtn1_iff : forall x y,
        clos_refl_trans R x y <-> clos_refl_trans_n1 R x y.
    Proof.
      split.
      apply clos_rt_rtn1.
      apply clos_rtn1_rt.
    Qed.

    (** Induction on the left transitive step *)

    Lemma clos_refl_trans_ind_left :
      forall (x:A) (P:A -> Prop), P x ->
	(forall y z:A, clos_refl_trans R x y -> P y -> R y z -> P z) ->
	forall z:A, clos_refl_trans R x z -> P z.
    Proof.
      intros.
      revert H H0.
      induction H1; intros; auto with sets.
      apply H1 with x; auto with sets.

      apply IHclos_refl_trans2.
      apply IHclos_refl_trans1; auto with sets.

      intros.
      apply H0 with y0; auto with sets.
      apply rt_trans with y; auto with sets.
    Qed.

    (** Induction on the right transitive step *)

    Lemma rt1n_ind_right : forall (P : A -> Prop) (z:A),
      P z ->
      (forall x y, R x y -> clos_refl_trans_1n R y z -> P y -> P x) ->
      forall x, clos_refl_trans_1n R x z -> P x.
      induction 3; auto.
      apply H0 with y; auto.
    Qed.

    Lemma clos_refl_trans_ind_right : forall (P : A -> Prop) (z:A),
      P z ->
      (forall x y, R x y -> P y -> clos_refl_trans R y z -> P x) ->
      forall x, clos_refl_trans R x z -> P x.
      intros P z Hz IH x Hxz.
      apply clos_rt_rt1n_iff in Hxz.
      elim Hxz using rt1n_ind_right; auto.
      clear x Hxz.
      intros x y Hxy Hyz Hy.
      apply clos_rt_rt1n_iff in Hyz.
      eauto.
    Qed.

    (** Direct reflexive-symmetric-transitive closure is equivalent to
        transitivity by symmetric left-step extension *)

    Lemma clos_rst1n_rst  : forall x y,
      clos_refl_sym_trans_1n R x y -> clos_refl_sym_trans R x y.
    Proof.
      induction 1.
      constructor 2.
      constructor 4 with y; auto.
      case H;[constructor 1|constructor 3; constructor 1]; auto.
    Qed.

    Lemma clos_rst1n_trans : forall x y z, clos_refl_sym_trans_1n R x y ->
        clos_refl_sym_trans_1n R y z -> clos_refl_sym_trans_1n R x z.
      induction 1.
      auto.
      intros; right with y; eauto.
    Qed.

    Lemma clos_rst1n_sym : forall x y, clos_refl_sym_trans_1n R x y ->
      clos_refl_sym_trans_1n R y x.
    Proof.
      intros x y H; elim H.
      constructor 1.
      intros x0 y0 z D H0 H1; apply clos_rst1n_trans with y0; auto.
      right with x0.
      tauto.
      left.
    Qed.

    Lemma clos_rst_rst1n  : forall x y,
      clos_refl_sym_trans R x y -> clos_refl_sym_trans_1n R x y.
      induction 1.
      constructor 2 with y; auto.
      constructor 1.
      constructor 1.
      apply clos_rst1n_sym; auto.
      eapply clos_rst1n_trans; eauto.
    Qed.

    Lemma clos_rst_rst1n_iff : forall x y,
      clos_refl_sym_trans R x y <-> clos_refl_sym_trans_1n R x y.
    Proof.
      split.
      apply clos_rst_rst1n.
      apply clos_rst1n_rst.
    Qed.

    (** Direct reflexive-symmetric-transitive closure is equivalent to
        transitivity by symmetric right-step extension *)

    Lemma clos_rstn1_rst : forall x y,
      clos_refl_sym_trans_n1 R x y -> clos_refl_sym_trans R x y.
    Proof.
      induction 1.
      constructor 2.
      constructor 4 with y; auto.
      case H;[constructor 1|constructor 3; constructor 1]; auto.
    Qed.

    Lemma clos_rstn1_trans : forall x y z, clos_refl_sym_trans_n1 R x y ->
      clos_refl_sym_trans_n1 R y z -> clos_refl_sym_trans_n1 R x z.
    Proof.
      intros x y z H1 H2.
      induction H2.
      auto.
      intros.
      right with y0; eauto.
    Qed.

    Lemma clos_rstn1_sym : forall x y, clos_refl_sym_trans_n1 R x y ->
      clos_refl_sym_trans_n1 R y x.
    Proof.
      intros x y H; elim H.
      constructor 1.
      intros y0 z D H0 H1. apply clos_rstn1_trans with y0; auto.
      right with z.
      tauto.
      left.
    Qed.

    Lemma clos_rst_rstn1 : forall x y,
      clos_refl_sym_trans R x y -> clos_refl_sym_trans_n1 R x y.
    Proof.
      induction 1.
      constructor 2 with x; auto.
      constructor 1.
      constructor 1.
      apply clos_rstn1_sym; auto.
      eapply clos_rstn1_trans; eauto.
    Qed.

    Lemma clos_rst_rstn1_iff : forall x y,
      clos_refl_sym_trans R x y <-> clos_refl_sym_trans_n1 R x y.
    Proof.
      split.
      apply clos_rst_rstn1.
      apply clos_rstn1_rst.
    Qed.

  End Equivalences.

  Lemma clos_trans_transp_permute : forall x y,
    transp _ (clos_trans R) x y <-> clos_trans (transp _ R) x y.
  Proof.
    split; induction 1;
    (apply t_step; assumption) || eapply t_trans; eassumption.
  Qed.

End Properties.

(* begin hide *)
(* Compatibility *)
Notation trans_tn1 := clos_trans_tn1 (only parsing).
Notation tn1_trans := clos_tn1_trans (only parsing).
Notation tn1_trans_equiv := clos_trans_tn1_iff (only parsing).

Notation trans_t1n := clos_trans_t1n (only parsing).
Notation t1n_trans := clos_t1n_trans (only parsing).
Notation t1n_trans_equiv := clos_trans_t1n_iff (only parsing).

Notation R_rtn1 := clos_rtn1_step (only parsing).
Notation trans_rt1n := clos_rt_rt1n (only parsing).
Notation rt1n_trans := clos_rt1n_rt (only parsing).
Notation rt1n_trans_equiv := clos_rt_rt1n_iff (only parsing).

Notation R_rt1n := clos_rt1n_step (only parsing).
Notation trans_rtn1 := clos_rt_rtn1 (only parsing).
Notation rtn1_trans := clos_rtn1_rt (only parsing).
Notation rtn1_trans_equiv := clos_rt_rtn1_iff (only parsing).

Notation rts1n_rts := clos_rst1n_rst (only parsing).
Notation rts_1n_trans := clos_rst1n_trans (only parsing).
Notation rts1n_sym := clos_rst1n_sym (only parsing).
Notation rts_rts1n := clos_rst_rst1n (only parsing).
Notation rts_rts1n_equiv := clos_rst_rst1n_iff (only parsing).

Notation rtsn1_rts := clos_rstn1_rst (only parsing).
Notation rtsn1_trans := clos_rstn1_trans (only parsing).
Notation rtsn1_sym := clos_rstn1_sym (only parsing).
Notation rts_rtsn1 := clos_rst_rstn1 (only parsing).
Notation rts_rtsn1_equiv := clos_rst_rstn1_iff (only parsing).
(* end hide *)
