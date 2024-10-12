(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
Require Import Inverse_Image.
Require Import Transitive_Closure.
Require Import List_Extension.
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
    - simple induction z.
      + simpl; intros H.
        inversion_clear H.
      + simpl; intros; apply (Lt_nil A leA).
    - intros a l HInd.
      simpl.
      intros.
      inversion_clear H.
      + apply (Lt_hd A leA); auto with sets.
      + apply (Lt_tl A leA).
        apply (HInd y y0); auto with sets.
  Qed.


  Lemma right_prefix :
    forall x y z : List,
      ltl x (y ++ z) ->
      ltl x y \/ (exists y' : List, x = y ++ y' /\ ltl y' z).
  Proof.
    intros x y; generalize x.
    elim y; simpl.
    - right.
      exists x0; auto with sets.
    - intros.
      inversion H0.
      + left; apply (Lt_nil A leA).
      + left; apply (Lt_hd A leA); auto with sets.
      + generalize (H x1 z H3).
        simple induction 1.
        * left; apply (Lt_tl A leA); auto with sets.
        * simple induction 1.
          simple induction 1; intros.
          rewrite H8.
          right; exists x2; auto with sets.
  Qed.

  Lemma desc_prefix : forall (x : List) (a : A), Descl (x ++ [a]) -> Descl x.
  Proof.
    intros x a H.
    inversion H as [| |????? E].
    - now destruct x.
    - now destruct x as [|?[|??]]; [constructor|..].
    - now apply app_inj_tail in E as (<-, _).
  Qed.

  Lemma desc_hd l : Descl l -> Forall (fun b => clos_refl_trans A leA b (hd b l)) l.
  Proof.
    intros H. induction H as [| |a' a'' l ? Hl IH].
    - easy.
    - now constructor; [apply rt_refl|].
    - enough (H' : Forall (fun b => clos_refl_trans A leA b (hd b (l ++ [a'']))) ((l ++ [a'']) ++ [a'])).
      { revert H'. apply Forall_impl. now destruct l. }
      apply Forall_app. split; [easy|].
      constructor; [|easy].
      eapply rt_trans.
      + apply clos_r_clos_rt. eassumption.
      + apply Forall_app in IH as [_ IH].
        destruct l as [|? l].
        * now apply rt_refl.
        * now apply Forall_cons_iff in IH as [??].
  Qed.

  Lemma desc_tail :
    forall (x : List) (a b : A),
      Descl (b :: x ++ [a]) -> clos_refl_trans A leA a b.
  Proof.
    intros ??? [_ H]%desc_hd%(Forall_app _ (_ :: _)).
    now apply Forall_cons_iff in H as [??].
  Qed.

  Lemma dist_Desc_concat :
    forall x y : List, Descl (x ++ y) -> Descl x /\ Descl y.
  Proof.
    intros x y H. split.
    - revert x H.
      induction y as [|a y IH] using rev_ind.
      + intros x. now rewrite app_nil_r.
      + intros x. rewrite app_assoc. now intros ?%desc_prefix%IH.
    - induction y as [|a y IH] using rev_ind; [repeat constructor|].
      induction y as [|a' y _] using rev_ind; [repeat constructor|].
      rewrite !app_assoc in H.
      inversion H as [| |????? E].
      + now destruct x, y.
      + now destruct x as [|? [|??]]; destruct y.
      + constructor.
        * apply app_inj_tail in E as [E <-].
          now apply app_inj_tail in E as [_ <-].
        * apply IH. rewrite app_assoc.
          now apply desc_prefix in H.
  Qed.

  Lemma desc_end :
    forall (a b : A) (x : List),
      Descl (x ++ [a]) /\ ltl (x ++ [a]) [b] -> clos_trans A leA a b.
  Proof.
    intros a b x.
    case x.
    - simpl.
      simple induction 1.
      intros.
      inversion H1; auto with sets.
      inversion H3.

    - simple induction 1.
      generalize (app_comm_cons l [a] a0).
      intros E; rewrite <- E; intros.
      generalize (desc_tail l a a0 H0); intro.
      inversion H1.
      + eapply clos_rt_t; [ eassumption | apply t_step; assumption ].

      + inversion H4.
  Qed.




  Lemma ltl_unit :
    forall (x : List) (a b : A),
      Descl (x ++ [a]) -> ltl (x ++ [a]) [b] -> ltl x [b].
  Proof.
    intro.
    case x.
    - intros; apply (Lt_nil A leA).

    - simpl; intros.
      inversion_clear H0.
      + apply (Lt_hd A leA a b); auto with sets.

      + inversion_clear H1.
  Qed.


  Lemma acc_app :
    forall (x1 x2 : List) (y1 : Descl (x1 ++ x2)),
      Acc Lex_Exp << x1 ++ x2, y1 >> ->
      forall (x : List) (y : Descl x),
        ltl x (x1 ++ x2) -> Acc Lex_Exp << x, y >>.
  Proof.
    intros.
    apply (Acc_inv (R:=Lex_Exp) (x:=<< x1 ++ x2, y1 >>)).
    - auto with sets.

    - unfold lex_exp; simpl; auto with sets.
  Qed.

  Theorem wf_lex_exp : well_founded leA -> well_founded Lex_Exp.
  Proof.
    intros wf_leA.
    eapply (wf_simulation _ _ _ (fun '(exist _ l _) l'  => l = l')).
    - apply wf_clos_trans. apply wf_list_ext. apply wf_clos_trans. apply wf_leA.
    - intros ? [l ?] _. now exists l.
    - unfold lex_exp. intros [l2 Hl2] [l1 Hl1]. cbn.
      intros ? H <-. exists l1. split; [reflexivity|].
      induction H as [|a b Hab l1 l2|].
      + now apply clos_trans_list_ext_nil_l.
      + assert (H'ab : clos_trans List (list_ext A (clos_trans A leA)) (a :: l1) [b]).
        { apply t_step. rewrite <-(app_nil_r (a :: l1)).
          eapply (list_ext_intro _ _ b (_ :: _) []).
          constructor; [now apply t_step|].
          apply desc_hd in Hl1.
          apply Forall_cons_iff in Hl1 as [_ Hl1].
          revert Hl1. apply Forall_impl.
          intros. eapply clos_rt_t; [|apply t_step]; eassumption. }
        rewrite <-(app_nil_r (a :: l1)).
        apply (clos_trans_list_ext_app_l _ _ _ _ [b]); [assumption|].
        destruct l2; [apply rt_refl|apply clos_t_clos_rt].
        now apply clos_trans_list_ext_nil_l.
      + apply (dist_Desc_concat [a]) in Hl1 as [_ ?].
        apply (dist_Desc_concat [a]) in Hl2 as [_ ?].
        apply (clos_trans_list_ext_app_r _ _ [a] _ [a]); auto using rt_refl.
  Qed.

End Wf_Lexicographic_Exponentiation.
