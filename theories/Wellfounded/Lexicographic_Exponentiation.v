(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Author: Cristina Cornes

    From : Constructing Recursion Operators in Type Theory
           L. Paulson  JSC (1986) 2, 325-355  *)

Require Import List.
Require Import Relation_Operators.
Require Import Transitive_Closure.

Section Wf_Lexicographic_Exponentiation.
  Variable A : Set.
  Variable leA : A -> A -> Prop.

  Notation Power := (Pow A leA).
  Notation Lex_Exp := (lex_exp A leA).
  Notation ltl := (Ltl A leA).
  Notation Descl := (Desc A leA).

  Notation List := (list A).
  Notation Nil := (nil (A:=A)).
  (* useless but symmetric *)
  Notation Cons := (cons (A:=A)).
  Notation "<< x , y >>" := (exist Descl x y) (at level 0, x, y at level 100).

  (* Hint Resolve d_one d_nil t_step. *)

  Lemma left_prefix : forall x y z:List, ltl (x ++ y) z -> ltl x z.
  Proof.
    simple induction x.
    simple induction z.
    simpl in |- *; intros H.
    inversion_clear H.
    simpl in |- *; intros; apply (Lt_nil A leA).
    intros a l HInd.
    simpl in |- *.
    intros.
    inversion_clear H.
    apply (Lt_hd A leA); auto with sets.
    apply (Lt_tl A leA).
    apply (HInd y y0); auto with sets.
  Qed.


  Lemma right_prefix :
    forall x y z:List,
      ltl x (y ++ z) -> ltl x y \/ (exists y' : List, x = y ++ y' /\ ltl y' z).
  Proof.
    intros x y; generalize x.
    elim y; simpl in |- *.
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

  Lemma desc_prefix : forall (x:List) (a:A), Descl (x ++ Cons a Nil) -> Descl x.
  Proof.
    intros.
    inversion H.
    generalize (app_cons_not_nil _ _ _ H1); simple induction 1.
    cut (x ++ Cons a Nil = Cons x0 Nil); auto with sets.
    intro.
    generalize (app_eq_unit _ _ H0).
    simple induction 1; simple induction 1; intros.
    rewrite H4; auto using d_nil with sets.
    discriminate H5.
    generalize (app_inj_tail _ _ _ _ H0).
    simple induction 1; intros.
    rewrite <- H4; auto with sets.
  Qed.

  Lemma desc_tail :
    forall (x:List) (a b:A),
      Descl (Cons b (x ++ Cons a Nil)) -> clos_trans A leA a b.
  Proof.
    intro.
    apply rev_ind with
      (A := A)
      (P := fun x:List =>
        forall a b:A,
          Descl (Cons b (x ++ Cons a Nil)) -> clos_trans A leA a b).
    intros.

    inversion H.
    cut (Cons b (Cons a Nil) = (Nil ++ Cons b Nil) ++ Cons a Nil);
      auto with sets; intro.
    generalize H0.
    intro.
    generalize (app_inj_tail (l ++ Cons y Nil) (Nil ++ Cons b Nil) _ _ H4);
      simple induction 1.
    intros.

    generalize (app_inj_tail _ _ _ _ H6); simple induction 1; intros.
    generalize H1.
    rewrite <- H10; rewrite <- H7; intro.
    apply (t_step A leA); auto with sets.

    intros.
    inversion H0.
    generalize (app_cons_not_nil _ _ _ H3); intro.
    elim H1.

    generalize H0.
    generalize (app_comm_cons (l ++ Cons x0 Nil) (Cons a Nil) b);
      simple induction 1.
    intro.
    generalize (desc_prefix (Cons b (l ++ Cons x0 Nil)) a H5); intro.
    generalize (H x0 b H6).
    intro.
    apply t_trans with (A := A) (y := x0); auto with sets.

    apply t_step.
    generalize H1.
    rewrite H4; intro.

    generalize (app_inj_tail _ _ _ _ H8); simple induction 1.
    intros.
    generalize H2; generalize (app_comm_cons l (Cons x0 Nil) b).
    intro.
    generalize H10.
    rewrite H12; intro.
    generalize (app_inj_tail _ _ _ _ H13); simple induction 1.
    intros.
    rewrite <- H11; rewrite <- H16; auto with sets.
  Qed.


  Lemma dist_aux :
    forall z:List, Descl z -> forall x y:List, z = x ++ y -> Descl x /\ Descl y.
  Proof.
    intros z D.
    elim D.
    intros.
    cut (x ++ y = Nil); auto with sets; intro.
    generalize (app_eq_nil _ _ H0); simple induction 1.
    intros.
    rewrite H2; rewrite H3; split; apply d_nil.

    intros.
    cut (x0 ++ y = Cons x Nil); auto with sets.
    intros E.
    generalize (app_eq_unit _ _ E); simple induction 1.
    simple induction 1; intros.
    rewrite H2; rewrite H3; split.
    apply d_nil.

    apply d_one.

    simple induction 1; intros.
    rewrite H2; rewrite H3; split.
    apply d_one.

    apply d_nil.

    do 5 intro.
    intros Hind.
    do 2 intro.
    generalize x0.
    apply rev_ind with
      (A := A)
      (P := fun y0:List =>
        forall x0:List,
          (l ++ Cons y Nil) ++ Cons x Nil = x0 ++ y0 ->
          Descl x0 /\ Descl y0).

    intro.
    generalize (app_nil_end x1); simple induction 1; simple induction 1.
    split. apply d_conc; auto with sets.

    apply d_nil.

    do 3 intro.
    generalize x1.
    apply rev_ind with
      (A := A)
      (P := fun l0:List =>
        forall (x1:A) (x0:List),
          (l ++ Cons y Nil) ++ Cons x Nil = x0 ++ l0 ++ Cons x1 Nil ->
          Descl x0 /\ Descl (l0 ++ Cons x1 Nil)).


    simpl in |- *.
    split.
    generalize (app_inj_tail _ _ _ _ H2); simple induction 1.
    simple induction 1; auto with sets.

    apply d_one.
    do 5 intro.
    generalize (app_ass x4 (l1 ++ Cons x2 Nil) (Cons x3 Nil)).
    simple induction 1.
    generalize (app_ass x4 l1 (Cons x2 Nil)); simple induction 1.
    intro E.
    generalize (app_inj_tail _ _ _ _ E).
    simple induction 1; intros.
    generalize (app_inj_tail _ _ _ _ H6); simple induction 1; intros.
    rewrite <- H7; rewrite <- H10; generalize H6.
    generalize (app_ass x4 l1 (Cons x2 Nil)); intro E1.
    rewrite E1.
    intro.
    generalize (Hind x4 (l1 ++ Cons x2 Nil) H11).
    simple induction 1; split.
    auto with sets.

    generalize H14.
    rewrite <- H10; intro.
    apply d_conc; auto with sets.
  Qed.



  Lemma dist_Desc_concat :
    forall x y:List, Descl (x ++ y) -> Descl x /\ Descl y.
  Proof.
    intros.
    apply (dist_aux (x ++ y) H x y); auto with sets.
  Qed.

  Lemma desc_end :
    forall (a b:A) (x:List),
      Descl (x ++ Cons a Nil) /\ ltl (x ++ Cons a Nil) (Cons b Nil) ->
      clos_trans A leA a b.
  Proof.
    intros a b x.
    case x.
    simpl in |- *.
    simple induction 1.
    intros.
    inversion H1; auto with sets.
    inversion H3.

    simple induction 1.
    generalize (app_comm_cons l (Cons a Nil) a0).
    intros E; rewrite <- E; intros.
    generalize (desc_tail l a a0 H0); intro.
    inversion H1.
    apply t_trans with (y := a0); auto with sets.

    inversion H4.
  Qed.




  Lemma ltl_unit :
    forall (x:List) (a b:A),
      Descl (x ++ Cons a Nil) ->
      ltl (x ++ Cons a Nil) (Cons b Nil) -> ltl x (Cons b Nil).
  Proof.
    intro.
    case x.
    intros; apply (Lt_nil A leA).

    simpl in |- *; intros.
    inversion_clear H0.
    apply (Lt_hd A leA a b); auto with sets.

    inversion_clear H1.
  Qed.


  Lemma acc_app :
    forall (x1 x2:List) (y1:Descl (x1 ++ x2)),
      Acc Lex_Exp << x1 ++ x2, y1 >> ->
      forall (x:List) (y:Descl x), ltl x (x1 ++ x2) -> Acc Lex_Exp << x, y >>.
  Proof.
    intros.
    apply (Acc_inv (R:=Lex_Exp) (x:=<< x1 ++ x2, y1 >>)).
    auto with sets.

    unfold lex_exp in |- *; simpl in |- *; auto with sets.
  Qed.


  Theorem wf_lex_exp : well_founded leA -> well_founded Lex_Exp.
  Proof.
    unfold well_founded at 2 in |- *.
    simple induction a; intros x y.
    apply Acc_intro.
    simple induction y0.
    unfold lex_exp at 1 in |- *; simpl in |- *.
    apply rev_ind with
      (A := A)
      (P := fun x:List =>
	forall (x0:List) (y:Descl x0), ltl x0 x -> Acc Lex_Exp << x0, y >>).
    intros.
    inversion_clear H0.

    intro.
    generalize (well_founded_ind (wf_clos_trans A leA H)).
    intros GR.
    apply GR with
      (P := fun x0:A =>
        forall l:List,
          (forall (x1:List) (y:Descl x1),
            ltl x1 l -> Acc Lex_Exp << x1, y >>) ->
          forall (x1:List) (y:Descl x1),
            ltl x1 (l ++ Cons x0 Nil) -> Acc Lex_Exp << x1, y >>).
    intro; intros HInd; intros.
    generalize (right_prefix x2 l (Cons x1 Nil) H1).
    simple induction 1.
    intro; apply (H0 x2 y1 H3).

    simple induction 1.
    intro; simple induction 1.
    clear H4 H2.
    intro; generalize y1; clear y1.
    rewrite H2.
    apply rev_ind with
      (A := A)
      (P := fun x3:List =>
        forall y1:Descl (l ++ x3),
          ltl x3 (Cons x1 Nil) -> Acc Lex_Exp << l ++ x3, y1 >>).
    intros.
    generalize (app_nil_end l); intros Heq.
    generalize y1.
    clear y1.
    rewrite <- Heq.
    intro.
    apply Acc_intro.
    simple induction y2.
    unfold lex_exp at 1 in |- *.
    simpl in |- *; intros x4 y3. intros.
    apply (H0 x4 y3); auto with sets.

    intros.
    generalize (dist_Desc_concat l (l0 ++ Cons x4 Nil) y1).
    simple induction 1.
    intros.
    generalize (desc_end x4 x1 l0 (conj H8 H5)); intros.
    generalize y1.
    rewrite <- (app_ass l l0 (Cons x4 Nil)); intro.
    generalize (HInd x4 H9 (l ++ l0)); intros HInd2.
    generalize (ltl_unit l0 x4 x1 H8 H5); intro.
    generalize (dist_Desc_concat (l ++ l0) (Cons x4 Nil) y2).
    simple induction 1; intros.
    generalize (H4 H12 H10); intro.
    generalize (Acc_inv H14).
    generalize (acc_app l l0 H12 H14).
    intros f g.
    generalize (HInd2 f); intro.
    apply Acc_intro.
    simple induction y3.
    unfold lex_exp at 1 in |- *; simpl in |- *; intros.
    apply H15; auto with sets.
  Qed.


End Wf_Lexicographic_Exponentiation.
