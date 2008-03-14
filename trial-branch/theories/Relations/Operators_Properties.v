(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(****************************************************************************)
(*                            Bruno Barras                                  *)
(****************************************************************************)

Require Import Relation_Definitions.
Require Import Relation_Operators.


Section Properties.

  Variable A : Type.
  Variable R : relation A.

  Let incl (R1 R2:relation A) : Prop := forall x y:A, R1 x y -> R2 x y.
  
  Section Clos_Refl_Trans.

    Lemma clos_rt_is_preorder : preorder A (clos_refl_trans A R).
    Proof.
      apply Build_preorder.
      exact (rt_refl A R).
      
      exact (rt_trans A R).
    Qed.

    Lemma clos_rt_idempotent :
      incl (clos_refl_trans A (clos_refl_trans A R)) (clos_refl_trans A R).
    Proof.
      red in |- *.
      induction 1; auto with sets.
      intros.
      apply rt_trans with y; auto with sets.
    Qed.

    Lemma clos_refl_trans_ind_left :
      forall (A:Type) (R:A -> A -> Prop) (M:A) (P:A -> Prop),
	P M ->
	(forall P0 N:A, clos_refl_trans A R M P0 -> P P0 -> R P0 N -> P N) ->
	forall a:A, clos_refl_trans A R M a -> P a.
    Proof.
      intros.
      generalize H H0.
      clear H H0.
      elim H1; intros; auto with sets.
      apply H2 with x; auto with sets.
      
      apply H3.
      apply H0; auto with sets.

      intros.
      apply H5 with P0; auto with sets.
      apply rt_trans with y; auto with sets.
    Qed.


  End Clos_Refl_Trans.


  Section Clos_Refl_Sym_Trans.

    Lemma clos_rt_clos_rst :
      inclusion A (clos_refl_trans A R) (clos_refl_sym_trans A R).
    Proof.
      red in |- *.
      induction 1; auto with sets.
      apply rst_trans with y; auto with sets.
    Qed.

    Lemma clos_rst_is_equiv : equivalence A (clos_refl_sym_trans A R).
    Proof.
      apply Build_equivalence.
      exact (rst_refl A R).
      exact (rst_trans A R).
      exact (rst_sym A R).
    Qed.

    Lemma clos_rst_idempotent :
      incl (clos_refl_sym_trans A (clos_refl_sym_trans A R))
      (clos_refl_sym_trans A R).
    Proof.
      red in |- *.
      induction 1; auto with sets.
      apply rst_trans with y; auto with sets.
    Qed.
  
  End Clos_Refl_Sym_Trans.

End Properties.
