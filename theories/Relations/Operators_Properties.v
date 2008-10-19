(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(************************************************************************)
(** * Some properties of the operators on relations                     *)
(************************************************************************)
(** * Initial version by Bruno Barras                                   *)
(************************************************************************)

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import Setoid.

Section Properties.

  Variable A : Type.
  Variable R : relation A.

  Let incl (R1 R2:relation A) : Prop := forall x y:A, R1 x y -> R2 x y.
  
  Section Clos_Refl_Trans.

    (** Correctness of the reflexive-transitive closure operator *)

    Lemma clos_rt_is_preorder : preorder A (clos_refl_trans A R).
    Proof.
      apply Build_preorder.
      exact (rt_refl A R).
      
      exact (rt_trans A R).
    Qed.

    (** Idempotency of the reflexive-transitive closure operator *)

    Lemma clos_rt_idempotent :
      incl (clos_refl_trans A (clos_refl_trans A R)) (clos_refl_trans A R).
    Proof.
      red in |- *.
      induction 1; auto with sets.
      intros.
      apply rt_trans with y; auto with sets.
    Qed.

  End Clos_Refl_Trans.

  Section Clos_Refl_Sym_Trans.

    (** Reflexive-transitive closure is included in the
        reflexive-symmetric-transitive closure *)

    Lemma clos_rt_clos_rst :
      inclusion A (clos_refl_trans A R) (clos_refl_sym_trans A R).
    Proof.
      red in |- *.
      induction 1; auto with sets.
      apply rst_trans with y; auto with sets.
    Qed.

    (** Correctness of the reflexive-symmetric-transitive closure *)

    Lemma clos_rst_is_equiv : equivalence A (clos_refl_sym_trans A R).
    Proof.
      apply Build_equivalence.
      exact (rst_refl A R).
      exact (rst_trans A R).
      exact (rst_sym A R).
    Qed.

    (** Idempotency of the reflexive-symmetric-transitive closure operator *)

    Lemma clos_rst_idempotent :
      incl (clos_refl_sym_trans A (clos_refl_sym_trans A R))
      (clos_refl_sym_trans A R).
    Proof.
      red in |- *.
      induction 1; auto with sets.
      apply rst_trans with y; auto with sets.
    Qed.

  End Clos_Refl_Sym_Trans.

  Section Equivalences.

  (** *** Equivalences between the different definition of the reflexive,
      symmetric, transitive closures *)

  (** *** Contributed by P. Casteran *)

    (** Direct transitive closure vs left-step extension *)

    Lemma t1n_trans : forall x y, clos_trans_1n A R x y -> clos_trans A R x y.
    Proof.
     induction 1.
     left; assumption.
     right with y; auto.
     left; auto.
    Qed.

    Lemma trans_t1n : forall x y, clos_trans A R x y -> clos_trans_1n A R x y.
    Proof.
      induction 1.
      left; assumption.
      generalize IHclos_trans2; clear IHclos_trans2; induction IHclos_trans1.
      right with y; auto.
      right with y; auto.
      eapply IHIHclos_trans1; auto.
      apply t1n_trans; auto.
    Qed.

    Lemma t1n_trans_equiv : forall x y, 
        clos_trans A R x y <-> clos_trans_1n A R x y.
    Proof.
      split.
      apply trans_t1n.
      apply t1n_trans.
    Qed.

    (** Direct transitive closure vs right-step extension *)

    Lemma tn1_trans : forall x y, clos_trans_n1 A R x y -> clos_trans A R x y.
    Proof.
      induction 1.
      left; assumption.
      right with y; auto.
      left; assumption.
    Qed.

    Lemma trans_tn1 :  forall x y, clos_trans A R x y -> clos_trans_n1 A R x y.
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

    Lemma tn1_trans_equiv : forall x y, 
        clos_trans A R x y <-> clos_trans_n1 A R x y.
    Proof.
      split.
      apply trans_tn1.
      apply tn1_trans.
    Qed.

    (** Direct reflexive-transitive closure is equivalent to 
        transitivity by left-step extension *)

    Lemma R_rt1n : forall x y, R x y -> clos_refl_trans_1n A R x y.
    Proof.
      intros x y H.
      right with y;[assumption|left].
    Qed.

    Lemma R_rtn1 : forall x y, R x y -> clos_refl_trans_n1 A R x y.
    Proof.
      intros x y H.
      right with x;[assumption|left].
    Qed.

    Lemma rt1n_trans : forall x y, 
        clos_refl_trans_1n A R x y -> clos_refl_trans A R x y.
    Proof.
      induction 1.
      constructor 2.
      constructor 3 with y; auto.
      constructor 1; auto.
    Qed.

    Lemma trans_rt1n : forall x y, 
        clos_refl_trans A R x y -> clos_refl_trans_1n A R x y.
    Proof.
      induction 1.
      apply R_rt1n; assumption.
      left.
      generalize IHclos_refl_trans2; clear IHclos_refl_trans2;
        induction IHclos_refl_trans1; auto.

      right with y; auto.
      eapply IHIHclos_refl_trans1; auto.
      apply rt1n_trans; auto.
    Qed.

    Lemma rt1n_trans_equiv : forall x y, 
      clos_refl_trans A R x y <-> clos_refl_trans_1n A R x y.
    Proof.
      split.
      apply trans_rt1n.
      apply rt1n_trans.
    Qed.

    (** Direct reflexive-transitive closure is equivalent to 
        transitivity by right-step extension *)

    Lemma rtn1_trans : forall x y,
        clos_refl_trans_n1 A R x y -> clos_refl_trans A R x y.
    Proof.
      induction 1.
      constructor 2.
      constructor 3 with y; auto.
      constructor 1; assumption.
    Qed.

    Lemma trans_rtn1 :  forall x y, 
        clos_refl_trans A R x y -> clos_refl_trans_n1 A R x y.
    Proof.
      induction 1.
      apply R_rtn1; auto.
      left.
      elim IHclos_refl_trans2; auto.
      intros.
      right with y0; auto.
    Qed.

    Lemma rtn1_trans_equiv : forall x y, 
        clos_refl_trans A R x y <-> clos_refl_trans_n1 A R x y.
    Proof.
      split.
      apply trans_rtn1.
      apply rtn1_trans.
    Qed.

    (** Induction on the left transitive step *)

    Lemma clos_refl_trans_ind_left :
      forall (x:A) (P:A -> Prop), P x ->
	(forall y z:A, clos_refl_trans A R x y -> P y -> R y z -> P z) ->
	forall z:A, clos_refl_trans A R x z -> P z.
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
      (forall x y, R x y -> clos_refl_trans_1n A R y z -> P y -> P x) ->
      forall x, clos_refl_trans_1n A R x z -> P x.
      induction 3; auto.
      apply H0 with y; auto.
    Qed.

    Lemma clos_refl_trans_ind_right : forall (P : A -> Prop) (z:A),
      P z ->
      (forall x y, R x y -> P y -> clos_refl_trans A R y z -> P x) ->
      forall x, clos_refl_trans A R x z -> P x.
      intros.
      rewrite rt1n_trans_equiv in H1.
      elim H1 using rt1n_ind_right; auto.
      intros; rewrite  <- rt1n_trans_equiv in *.
      eauto.
    Qed.

    (** Direct reflexive-symmetric-transitive closure is equivalent to 
        transitivity by symmetric left-step extension *)

    Lemma rts1n_rts  : forall x y, 
      clos_refl_sym_trans_1n A R x y -> clos_refl_sym_trans A R x y.
    Proof.
      induction 1.
      constructor 2.
      constructor 4 with y; auto.
      case H;[constructor 1|constructor 3; constructor 1]; auto.
    Qed.

    Lemma rts_1n_trans : forall x y, clos_refl_sym_trans_1n A R x y ->
      forall z, clos_refl_sym_trans_1n A R y z -> 
        clos_refl_sym_trans_1n A R x z.
      induction 1.
      auto.
      intros; right with y; eauto.
    Qed.

    Lemma rts1n_sym : forall x y, clos_refl_sym_trans_1n A R x y ->
      clos_refl_sym_trans_1n A R y x.
    Proof.
      intros x y H; elim H.
      constructor 1.
      intros x0 y0 z D H0 H1; apply rts_1n_trans with y0; auto.
      right with x0.
      tauto.
      left.
    Qed.

    Lemma rts_rts1n  : forall x y, 
      clos_refl_sym_trans A R x y -> clos_refl_sym_trans_1n A R x y.
      induction 1.
      constructor 2 with y; auto.
      constructor 1.
      constructor 1.
      apply rts1n_sym; auto.
      eapply rts_1n_trans; eauto.
    Qed.

    Lemma rts_rts1n_equiv : forall x y, 
      clos_refl_sym_trans A R x y <-> clos_refl_sym_trans_1n A R x y.
    Proof.
      split.
      apply rts_rts1n.
      apply rts1n_rts.
    Qed.

    (** Direct reflexive-symmetric-transitive closure is equivalent to 
        transitivity by symmetric right-step extension *)

    Lemma rtsn1_rts : forall x y, 
      clos_refl_sym_trans_n1 A R x y -> clos_refl_sym_trans A R x y.
    Proof.
      induction 1.
      constructor 2.
      constructor 4 with y; auto.
      case H;[constructor 1|constructor 3; constructor 1]; auto.
    Qed.

    Lemma rtsn1_trans : forall y z, clos_refl_sym_trans_n1 A R y z->
      forall x, clos_refl_sym_trans_n1 A R x y -> 
        clos_refl_sym_trans_n1 A R x z.
    Proof.
      induction 1.
      auto.
      intros.
      right with y0; eauto.
    Qed.

    Lemma rtsn1_sym : forall x y, clos_refl_sym_trans_n1 A R x y ->
      clos_refl_sym_trans_n1 A R y x.
    Proof.
      intros x y H; elim H.
      constructor 1.
      intros y0 z D H0 H1. apply rtsn1_trans with y0; auto.
      right with z.
      tauto.
      left.
    Qed.

    Lemma rts_rtsn1 : forall x y, 
      clos_refl_sym_trans A R x y -> clos_refl_sym_trans_n1 A R x y.
    Proof.
      induction 1.
      constructor 2 with x; auto.
      constructor 1.
      constructor 1.
      apply rtsn1_sym; auto.
      eapply rtsn1_trans; eauto.
    Qed.

    Lemma rts_rtsn1_equiv : forall x y, 
      clos_refl_sym_trans A R x y <-> clos_refl_sym_trans_n1 A R x y.
    Proof.
      split.
      apply rts_rtsn1.
      apply rtsn1_rts.
    Qed.

  End Equivalences.

End Properties.
