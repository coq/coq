(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Author: Cristina Cornes

    From : Constructing Recursion Operators in Type Theory
           L. Paulson  JSC (1986) 2, 325-355  *)

Require Import List.
Require Import Relation_Operators.
Require Import Operators_Properties.
Require Import Transitive_Closure.

Import ListNotations.

Section Wf_Lexicographic_Exponentiation.
  Variable A : Set.
  Variable leA : A -> A -> Prop.

  Notation Power := (Pow A leA).
  Notation Lex_Exp := (lex_exp A leA).
  Notation ltl := (Ltl A leA).
  Notation Descl := (Desc A leA).

  Notation List := (list A).
  Notation "<< x , y >>" := (exist Descl x y) (at level 0, x, y at level 100).

  (* Hint Resolve d_one d_nil t_step. *)

  Lemma left_prefix : forall x y z : List, ltl (x ++ y) z -> ltl x z.
  Proof.
    simple induction x.
    simple induction z.
    simpl; intros H.
    inversion_clear H.
    simpl; intros; apply (Lt_nil A leA).
    intros a l HInd.
    simpl.
    intros.
    inversion_clear H.
    apply (Lt_hd A leA); auto with sets.
    apply (Lt_tl A leA).
    apply (HInd y y0); auto with sets.
  Qed.


  Lemma right_prefix :
    forall x y z : List,
      ltl x (y ++ z) ->
      ltl x y \/ (exists y' : List, x = y ++ y' /\ ltl y' z).
  Proof.
    intros x y; generalize x.
    elim y; simpl.
    right.
    exists x0; auto with sets.
    intros.
    inversion H0.
    left; apply (Lt_nil A leA).
    left; apply (Lt_hd A leA); auto with sets.
    generalize (H x1 z H3).
    simple induction 1.
    left; apply (Lt_tl A leA); auto with sets.
    simple induction 1.
    simple induction 1; intros.
    rewrite H8.
    right; exists x2; auto with sets.
  Qed.

  Lemma desc_prefix : forall (x : List) (a : A), Descl (x ++ [a]) -> Descl x.
  Proof.
    intros.
    inversion H.
    - apply app_cons_not_nil in H1 as [].
    - assert (x ++ [a] = [x0]) by auto with sets.
      apply app_eq_unit in H0 as [(->, _)| (_, [=])].
      auto using d_nil.
    - apply app_inj_tail in H0 as (<-, _).
      assumption.
  Qed.

  Lemma desc_tail :
    forall (x : List) (a b : A),
      Descl (b :: x ++ [a]) -> clos_refl_trans A leA a b.
  Proof.
    intro.
    apply rev_ind with
      (P := 
        fun x : List =>
        forall a b : A, Descl (b :: x ++ [a]) -> clos_refl_trans A leA a b);
     intros.
    - inversion H.
      assert ([b; a] = ([] ++ [b]) ++ [a]) by auto with sets.
      destruct (app_inj_tail (l ++ [y]) ([] ++ [b]) _ _ H0) as ((?, <-)%app_inj_tail, <-).
      inversion H1; subst; [ apply rt_step; assumption | apply rt_refl ].
    - inversion H0.
      + apply app_cons_not_nil in H3 as [].
      + rewrite app_comm_cons in H0, H1. apply desc_prefix in H0.
        pose proof (H x0 b H0).
        apply rt_trans with (y := x0); auto with sets.
        enough (H5 : clos_refl A leA a x0)
         by (inversion H5; subst; [ apply rt_step | apply rt_refl ];
              assumption).
        apply app_inj_tail in H1 as (H1, ->).
        rewrite app_comm_cons in H1.
        apply app_inj_tail in H1 as (_, <-).
        assumption.
  Qed.


  Lemma dist_aux :
    forall z : List,
      Descl z -> forall x y : List, z = x ++ y -> Descl x /\ Descl y.
  Proof.
    intros z D.
    induction D as [| | * H D Hind]; intros.
    - assert (H0 : x ++ y = []) by auto with sets.
      apply app_eq_nil in H0 as (->, ->).
      split; apply d_nil.
    - assert (E : x0 ++ y = [x]) by auto with sets.
      apply app_eq_unit in E as [(->, ->)| (->, ->)].
      + split.
        apply d_nil.
        apply d_one.
      + split.
        apply d_one.
        apply d_nil.
    - induction y0 using rev_ind in x0, H0 |- *.
      + rewrite <- app_nil_end in H0.
        rewrite <- H0.
        split.
        apply d_conc; auto with sets.
        apply d_nil.
      + induction y0 using rev_ind in x1, x0, H0 |- *.
        * simpl.
          split.
          apply app_inj_tail in H0 as (<-, _). assumption.
          apply d_one.
        * rewrite <- 2!app_assoc_reverse in H0.
          apply app_inj_tail in H0 as (H0, <-).
          pose proof H0 as H0'.
          apply app_inj_tail in H0' as (_, ->).
          rewrite app_assoc_reverse in H0.
          apply Hind in H0 as [].
          split.
          assumption.
          apply d_conc; auto with sets.
  Qed.



  Lemma dist_Desc_concat :
    forall x y : List, Descl (x ++ y) -> Descl x /\ Descl y.
  Proof.
    intros.
    apply (dist_aux (x ++ y) H x y); auto with sets.
  Qed.

  Lemma desc_end :
    forall (a b : A) (x : List),
      Descl (x ++ [a]) /\ ltl (x ++ [a]) [b] -> clos_trans A leA a b.
  Proof.
    intros a b x.
    case x.
    simpl.
    simple induction 1.
    intros.
    inversion H1; auto with sets.
    inversion H3.

    simple induction 1.
    generalize (app_comm_cons l [a] a0).
    intros E; rewrite <- E; intros.
    generalize (desc_tail l a a0 H0); intro.
    inversion H1.
    eapply clos_rt_t; [ eassumption | apply t_step; assumption ].

    inversion H4.
  Qed.




  Lemma ltl_unit :
    forall (x : List) (a b : A),
      Descl (x ++ [a]) -> ltl (x ++ [a]) [b] -> ltl x [b].
  Proof.
    intro.
    case x.
    intros; apply (Lt_nil A leA).

    simpl; intros.
    inversion_clear H0.
    apply (Lt_hd A leA a b); auto with sets.

    inversion_clear H1.
  Qed.


  Lemma acc_app :
    forall (x1 x2 : List) (y1 : Descl (x1 ++ x2)),
      Acc Lex_Exp << x1 ++ x2, y1 >> ->
      forall (x : List) (y : Descl x),
        ltl x (x1 ++ x2) -> Acc Lex_Exp << x, y >>.
  Proof.
    intros.
    apply (Acc_inv (R:=Lex_Exp) (x:=<< x1 ++ x2, y1 >>)).
    auto with sets.

    unfold lex_exp; simpl; auto with sets.
  Qed.


  Theorem wf_lex_exp : well_founded leA -> well_founded Lex_Exp.
  Proof.
    unfold well_founded at 2.
    simple induction a; intros x y.
    apply Acc_intro.
    simple induction y0.
    unfold lex_exp at 1; simpl.
    apply rev_ind with
      (A := A)
      (P := 
        fun x : List =>
        forall (x0 : List) (y : Descl x0),
          ltl x0 x -> Acc Lex_Exp << x0, y >>).
    intros.
    inversion_clear H0.

    intro.
    generalize (well_founded_ind (wf_clos_trans A leA H)).
    intros GR.
    apply GR with
      (P := 
        fun x0 : A =>
        forall l : List,
          (forall (x1 : List) (y : Descl x1),
             ltl x1 l -> Acc Lex_Exp << x1, y >>) ->
          forall (x1 : List) (y : Descl x1),
            ltl x1 (l ++ [x0]) -> Acc Lex_Exp << x1, y >>).
    intro; intros HInd; intros.
    generalize (right_prefix x2 l [x1] H1).
    simple induction 1.
    intro; apply (H0 x2 y1 H3).

    simple induction 1.
    intro; simple induction 1.
    clear H4 H2.
    intro; generalize y1; clear y1.
    rewrite H2.
    apply rev_ind with
      (A := A)
      (P := 
        fun x3 : List =>
        forall y1 : Descl (l ++ x3),
          ltl x3 [x1] -> Acc Lex_Exp << l ++ x3, y1 >>).
    intros.
    generalize (app_nil_end l); intros Heq.
    generalize y1.
    clear y1.
    rewrite <- Heq.
    intro.
    apply Acc_intro.
    simple induction y2.
    unfold lex_exp at 1.
    simpl; intros x4 y3. intros.
    apply (H0 x4 y3); auto with sets.

    intros.
    generalize (dist_Desc_concat l (l0 ++ [x4]) y1).
    simple induction 1.
    intros.
    generalize (desc_end x4 x1 l0 (conj H8 H5)); intros.
    generalize y1.
    rewrite <- (app_assoc_reverse l l0 [x4]); intro.
    generalize (HInd x4 H9 (l ++ l0)); intros HInd2.
    generalize (ltl_unit l0 x4 x1 H8 H5); intro.
    generalize (dist_Desc_concat (l ++ l0) [x4] y2).
    simple induction 1; intros.
    generalize (H4 H12 H10); intro.
    generalize (Acc_inv H14).
    generalize (acc_app l l0 H12 H14).
    intros f g.
    generalize (HInd2 f); intro.
    apply Acc_intro.
    simple induction y3.
    unfold lex_exp at 1; simpl; intros.
    apply H15; auto with sets.
  Qed.


End Wf_Lexicographic_Exponentiation.
