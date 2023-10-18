Require Import List.
Require Import Relation_Operators Operators_Properties.
Import ListNotations.

(** Author: Andrej Dudenhefner *)

Section WfList_Extension.

  Variable A : Type.
  Variable ltA : A -> A -> Prop.

  (* List extension of the relation ltA *)
  Inductive list_ext : list A -> list A -> Prop :=
    | list_ext_intro a (bs : list A) l1 l2 :
        Forall (fun b => ltA b a) bs -> list_ext (l1 ++ bs ++ l2) (l1 ++ a :: l2).

  Lemma list_ext_inv l l' : list_ext l l' ->
    exists a bs l1 l2, l = l1 ++ bs ++ l2 /\ l' = l1 ++ a :: l2 /\ Forall (fun b => ltA b a) bs.
  Proof.
    intros H. destruct H.
    now repeat econstructor.
  Qed.

  Lemma list_ext_nil_r l : not (list_ext l []).
  Proof.
    now intros [? [? [[|??] [? [? [? ?]]]]]]%list_ext_inv.
  Qed.

  Lemma list_ext_Acc_app l1 l2 : Acc list_ext l1 -> Acc list_ext l2 -> Acc list_ext (l1 ++ l2).
  Proof.
    intros H. revert l2. induction H as [l1 _ IH1].
    intros l2 H. induction H as [l2 Hl2 IH2].
    constructor. intros l [a [bs [l'1 [l'2 [? [E ?]]]]]]%list_ext_inv.
    apply app_eq_app in E as [l'' [[? Hl'']|[? ?]]]; subst.
    - destruct l'' as [|??]; cbn in Hl''.
      + rewrite app_nil_r in IH2.
        apply IH2. subst.
        now apply (list_ext_intro a bs nil).
      + injection Hl'' as [=? ?]. subst.
        rewrite !app_assoc. apply IH1.
        * rewrite <- !app_assoc. now constructor.
        * constructor. now apply Hl2.
    - rewrite <- !app_assoc.
      apply IH2. now constructor.
  Defined.

  Lemma Acc_list_ext l : Forall (Acc ltA) l -> Acc list_ext l.
  Proof.
    intros H. induction H as [|a l Ha ??].
    - constructor. now intros ? ?%list_ext_nil_r.
    - apply (list_ext_Acc_app [_]); [|assumption].
      clear -Ha. induction Ha as [a _ IH].
      constructor. intros l H%list_ext_inv.
      destruct H as [a' [bs [[|? [|? ?]] [[|??] [E1 [E2 Hbs]]]]]]; [|easy..].
      cbn in *. injection E2 as [= E2]. subst.
      rewrite app_nil_r. induction Hbs.
      + constructor. now intros ? ?%list_ext_nil_r.
      + now apply (list_ext_Acc_app [_]); [apply IH|].
  Defined.

  Theorem wf_list_ext : well_founded ltA -> well_founded list_ext.
  Proof.
    intros H l. apply Acc_list_ext.
    apply Forall_forall. intros. now apply H.
  Defined.

  Lemma clos_trans_list_ext_nil_l l : l <> [] -> clos_trans (list A) list_ext [] l.
  Proof.
    induction l as [|a l IH]; [easy|].
    intros _. destruct l as [|a' l].
    - apply t_step. now apply (list_ext_intro a [] []).
    - eapply t_trans.
      + now apply IH.
      + apply t_step.
        now apply (list_ext_intro a [] [] (_ :: _)).
  Qed.

  Lemma list_ext_app_l l1 l2 l : list_ext l1 l2 -> list_ext (l1 ++ l) (l2 ++ l).
  Proof.
    intros [] *. rewrite <- !app_assoc. now constructor.
  Qed.

  Lemma list_ext_app_r l l1 l2 : list_ext l1 l2 -> list_ext (l ++ l1) (l ++ l2).
  Proof.
    intros [a bs l'1 l'2 H]. rewrite !(app_assoc l l'1). now constructor.
  Qed.

  Lemma clos_refl_trans_list_ext_app_l l1 l2 l : clos_refl_trans (list A) list_ext l1 l2 -> clos_refl_trans (list A) list_ext (l1 ++ l) (l2 ++ l).
  Proof.
    intros H. induction H; intros.
    - apply rt_step. now apply list_ext_app_l.
    - now constructor.
    - eapply rt_trans; eassumption.
  Qed.

  Lemma clos_refl_trans_list_ext_app_r l l1 l2 : clos_refl_trans (list A) list_ext l1 l2 -> clos_refl_trans (list A) list_ext (l ++ l1) (l ++ l2).
  Proof.
    intros H. induction H; intros.
    - apply rt_step. now apply list_ext_app_r.
    - now constructor.
    - eapply rt_trans; eassumption.
  Qed.

  Lemma clos_trans_list_ext_app_l l1 l2 l3 l4 :
    clos_trans (list A) list_ext l1 l3 ->
    clos_refl_trans (list A) list_ext l2 l4 ->
    clos_trans (list A) list_ext (l1 ++ l2) (l3 ++ l4).
  Proof.
    intros H ?. eapply clos_rt_t.
    - apply clos_refl_trans_list_ext_app_r. eassumption.
    - induction H; intros.
      + apply t_step. now apply list_ext_app_l.
      + eapply t_trans; eassumption.
  Qed.

  Lemma clos_trans_list_ext_app_r l1 l2 l3 l4 :
    clos_refl_trans (list A) list_ext l1 l3 ->
    clos_trans (list A) list_ext l2 l4 ->
    clos_trans (list A) list_ext (l1 ++ l2) (l3 ++ l4).
  Proof.
    intros ? H. eapply clos_rt_t.
    - apply clos_refl_trans_list_ext_app_l. eassumption.
    - induction H; intros.
      + apply t_step. now apply list_ext_app_r.
      + eapply t_trans; eassumption.
  Qed.

End WfList_Extension.
