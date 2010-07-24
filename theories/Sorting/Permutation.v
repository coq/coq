(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*********************************************************************)
(** ** List permutations as a composition of adjacent transpositions *)
(*********************************************************************)

(* Adapted in May 2006 by Jean-Marc Notin from initial contents by
   Laurent Théry (Huffmann contribution, October 2003) *)

Require Import List Setoid.

Set Implicit Arguments.

Local Notation "[ ]" := nil.
Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..).

Section Permutation.

Variable A:Type.

Inductive Permutation : list A -> list A -> Prop :=
| perm_nil: Permutation [] []
| perm_skip x l l' : Permutation l l' -> Permutation (x::l) (x::l')
| perm_swap x y l : Permutation (y::x::l) (x::y::l)
| perm_trans l l' l'' : Permutation l l' -> Permutation l' l'' -> Permutation l l''.

Local Hint Constructors Permutation.

(** Some facts about [Permutation] *)

Theorem Permutation_nil : forall (l : list A), Permutation [] l -> l = [].
Proof.
  intros l HF.
  remember (@nil A) as m in HF.
  induction HF; discriminate || auto.
Qed.

Theorem Permutation_nil_cons : forall (l : list A) (x : A), ~ Permutation nil (x::l).
Proof.
  intros l x HF.
  apply Permutation_nil in HF; discriminate.
Qed.

(** Permutation over lists is a equivalence relation *)

Theorem Permutation_refl : forall l : list A, Permutation l l.
Proof.
  induction l; constructor. exact IHl.
Qed.

Theorem Permutation_sym : forall l l' : list A, Permutation l l' -> Permutation l' l.
Proof.
  intros l l' Hperm; induction Hperm; auto.
  apply perm_trans with (l':=l'); assumption.
Qed.

Theorem Permutation_trans : forall l l' l'' : list A, Permutation l l' -> Permutation l' l'' -> Permutation l l''.
Proof.
  exact perm_trans.
Qed.

End Permutation.

Hint Resolve Permutation_refl perm_nil perm_skip.

(* These hints do not reduce the size of the problem to solve and they
   must be used with care to avoid combinatoric explosions *)

Local Hint Resolve perm_swap perm_trans.
Local Hint Resolve Permutation_sym Permutation_trans.

(* This provides reflexivity, symmetry and transitivity and rewriting
   on morphims to come *)

Instance Permutation_Equivalence A : Equivalence (@Permutation A) | 10 := {
  Equivalence_Reflexive := @Permutation_refl A ;
  Equivalence_Symmetric := @Permutation_sym A ;
  Equivalence_Transitive := @Permutation_trans A }.

Add Parametric Morphism A (a:A) : (cons a)
  with signature @Permutation A ==> @Permutation A
  as Permutation_cons.
Proof.
  auto using perm_skip.
Qed.

Section Permutation_properties.

Variable A:Type.

Implicit Types a b : A.
Implicit Types l m : list A.

(** Compatibility with others operations on lists *)

Theorem Permutation_in : forall (l l' : list A) (x : A), Permutation l l' -> In x l -> In x l'.
Proof.
  intros l l' x Hperm; induction Hperm; simpl; tauto.
Qed.

Lemma Permutation_app_tail : forall (l l' tl : list A), Permutation l l' -> Permutation (l++tl) (l'++tl).
Proof.
  intros l l' tl Hperm; induction Hperm as [|x l l'|x y l|l l' l'']; simpl; auto.
  eapply Permutation_trans with (l':=l'++tl); trivial.
Qed.

Lemma Permutation_app_head : forall (l tl tl' : list A), Permutation tl tl' -> Permutation (l++tl) (l++tl').
Proof.
  intros l tl tl' Hperm; induction l; [trivial | repeat rewrite <- app_comm_cons; constructor; assumption].
Qed.

Theorem Permutation_app : forall (l m l' m' : list A), Permutation l l' -> Permutation m m' -> Permutation (l++m) (l'++m').
Proof.
  intros l m l' m' Hpermll' Hpermmm'; induction Hpermll' as [|x l l'|x y l|l l' l'']; repeat rewrite <- app_comm_cons; auto.
  apply Permutation_trans with (l' := (x :: y :: l ++ m));
	[idtac | repeat rewrite app_comm_cons; apply Permutation_app_head]; trivial.
  apply Permutation_trans with (l' := (l' ++ m')); try assumption.
  apply Permutation_app_tail; assumption.
Qed.

Add Parametric Morphism : (@app A)
  with signature @Permutation A ==> @Permutation A ==> @Permutation A
  as Permutation_app'.
  auto using Permutation_app.
Qed.

Lemma Permutation_add_inside : forall a (l l' tl tl' : list A),
  Permutation l l' -> Permutation tl tl' ->
  Permutation (l ++ a :: tl) (l' ++ a :: tl').
Proof.
  intros; apply Permutation_app; auto.
Qed.

Theorem Permutation_app_comm : forall (l l' : list A),
  Permutation (l ++ l') (l' ++ l).
Proof.
  induction l as [|x l]; simpl; intro l'.
  rewrite app_nil_r; trivial.
  induction l' as [|y l']; simpl.
  rewrite app_nil_r; trivial.
  transitivity (x :: y :: l' ++ l).
  constructor; rewrite app_comm_cons; apply IHl.
  transitivity (y :: x :: l' ++ l); constructor.
  transitivity (x :: l ++ l'); auto.
Qed.

Theorem Permutation_cons_app : forall (l l1 l2:list A) a,
  Permutation l (l1 ++ l2) -> Permutation (a :: l) (l1 ++ a :: l2).
Proof.
  intros l l1; revert l.
  induction l1.
  simpl.
  intros; apply perm_skip; auto.
  simpl; intros.
  transitivity (a0::a::l1++l2).
  apply perm_skip; auto.
  transitivity (a::a0::l1++l2).
  apply perm_swap; auto.
  apply perm_skip; auto.
Qed.
Local Hint Resolve Permutation_cons_app.

Theorem Permutation_middle : forall (l1 l2:list A) a,
  Permutation (a :: l1 ++ l2) (l1 ++ a :: l2).
Proof.
  auto.
Qed.

Theorem Permutation_rev : forall (l : list A), Permutation l (rev l).
Proof.
  induction l as [| x l]; simpl; trivial.
  apply Permutation_trans with (l' := [x] ++ rev l).
  simpl; auto.
  apply Permutation_app_comm.
Qed.

Theorem Permutation_length : forall (l l' : list A), Permutation l l' -> length l = length l'.
Proof.
  intros l l' Hperm; induction Hperm; simpl; auto.
  apply trans_eq with (y:= (length l')); trivial.
Qed.

Theorem Permutation_ind_bis :
 forall P : list A -> list A -> Prop,
   P [] [] ->
   (forall x l l', Permutation l l' -> P l l' -> P (x :: l) (x :: l')) ->
   (forall x y l l', Permutation l l' -> P l l' -> P (y :: x :: l) (x :: y :: l')) ->
   (forall l l' l'', Permutation l l' -> P l l' -> Permutation l' l'' -> P l' l'' -> P l l'') ->
   forall l l', Permutation l l' -> P l l'.
Proof.
  intros P Hnil Hskip Hswap Htrans.
  induction 1; auto.
  apply Htrans with (x::y::l); auto.
  apply Hswap; auto.
  induction l; auto.
  apply Hskip; auto.
  apply Hskip; auto.
  induction l; auto.
  eauto.
Qed.

Ltac break_list l x l' H :=
  destruct l as [|x l']; simpl in *;
  injection H; intros; subst; clear H.

Theorem Permutation_app_inv : forall (l1 l2 l3 l4:list A) a,
  Permutation (l1++a::l2) (l3++a::l4) -> Permutation (l1++l2) (l3 ++ l4).
Proof.
  set (P l l' :=
         forall a l1 l2 l3 l4, l=l1++a::l2 -> l'=l3++a::l4 -> Permutation (l1++l2) (l3++l4)).
  cut (forall l l', Permutation l l' -> P l l').
  intros; apply (H _ _ H0 a); auto.
  intros; apply (Permutation_ind_bis P); unfold P; clear P; try clear H l l'; simpl; auto.
(* nil *)
  intros; destruct l1; simpl in *; discriminate.
  (* skip *)
  intros x l l' H IH; intros.
  break_list l1 b l1' H0; break_list l3 c l3' H1.
  auto.
  apply perm_trans with (l3'++c::l4); auto.
  apply perm_trans with (l1'++a::l2); auto using Permutation_cons_app.
  apply perm_skip.
  apply (IH a l1' l2 l3' l4); auto.
  (* contradict *)
  intros x y l l' Hp IH; intros.
  break_list l1 b l1' H; break_list l3 c l3' H0.
  auto.
  break_list l3' b l3'' H.
  auto.
  apply perm_trans with (c::l3''++b::l4); auto.
  break_list l1' c l1'' H1.
  auto.
  apply perm_trans with (b::l1''++c::l2); auto.
  break_list l3' d l3'' H; break_list l1' e l1'' H1.
  auto.
  apply perm_trans with (e::a::l1''++l2); auto.
  apply perm_trans with (e::l1''++a::l2); auto.
  apply perm_trans with (d::a::l3''++l4); auto.
  apply perm_trans with (d::l3''++a::l4); auto.
  apply perm_trans with (e::d::l1''++l2); auto.
  apply perm_skip; apply perm_skip.
  apply (IH a l1'' l2 l3'' l4); auto.
  (*trans*)
  intros.
  destruct (In_split a l') as (l'1,(l'2,H6)).
  apply (Permutation_in a H).
  subst l.
  apply in_or_app; right; red; auto.
  apply perm_trans with (l'1++l'2).
  apply (H0 _ _ _ _ _ H3 H6).
  apply (H2 _ _ _ _ _ H6 H4).
Qed.

Theorem Permutation_cons_inv :
   forall l l' a, Permutation (a::l) (a::l') -> Permutation l l'.
Proof.
  intros; exact (Permutation_app_inv [] l [] l' a H).
Qed.

Theorem Permutation_cons_app_inv :
   forall l l1 l2 a, Permutation (a :: l) (l1 ++ a :: l2) -> Permutation l (l1 ++ l2).
Proof.
  intros; exact (Permutation_app_inv [] l l1 l2 a H).
Qed.

Theorem Permutation_app_inv_l :
    forall l l1 l2, Permutation (l ++ l1) (l ++ l2) -> Permutation l1 l2.
Proof.
  induction l; simpl; auto.
  intros.
  apply IHl.
  apply Permutation_cons_inv with a; auto.
Qed.

Theorem Permutation_app_inv_r :
   forall l l1 l2, Permutation (l1 ++ l) (l2 ++ l) -> Permutation l1 l2.
Proof.
  induction l.
  intros l1 l2; do 2 rewrite app_nil_r; auto.
  intros.
  apply IHl.
  apply Permutation_app_inv with a; auto.
Qed.

Lemma Permutation_length_1_inv: forall a l, Permutation [a] l -> l = [a].
Proof.
  intros a l H; remember [a] as m in H.
  induction H; try (injection Heqm as -> ->; clear Heqm);
    discriminate || auto.
  apply Permutation_nil in H as ->; trivial.
Qed.

Lemma Permutation_length_1: forall a b, Permutation [a] [b] -> a = b.
Proof.
  intros a b H.
  apply Permutation_length_1_inv in H; injection H as ->; trivial.
Qed.

Lemma Permutation_length_2_inv :
  forall a1 a2 l, Permutation [a1;a2] l -> l = [a1;a2] \/ l = [a2;a1].
Proof.
  intros a1 a2 l H; remember [a1;a2] as m in H.
  revert a1 a2 Heqm.
  induction H; intros; try (injection Heqm; intros; subst; clear Heqm);
    discriminate || (try tauto).
  apply Permutation_length_1_inv in H as ->; left; auto.
  apply IHPermutation1 in Heqm as [H1|H1]; apply IHPermutation2 in H1 as ();
    auto.
Qed.

Lemma Permutation_length_2 :
  forall a1 a2 b1 b2, Permutation [a1;a2] [b1;b2] ->
    a1 = b1 /\ a2 = b2 \/ a1 = b2 /\ a2 = b1.
Proof.
  intros a1 b1 a2 b2 H.
  apply Permutation_length_2_inv in H as [H|H]; injection H as -> ->; auto.
Qed.

Lemma NoDup_Permutation : forall l l',
  NoDup l -> NoDup l' -> (forall x:A, In x l <-> In x l') -> Permutation l l'.
Proof.
  induction l.
  destruct l'; simpl; intros.
  apply perm_nil.
  destruct (H1 a) as (_,H2); destruct H2; auto.
  intros.
  destruct (In_split a l') as (l'1,(l'2,H2)).
  destruct (H1 a) as (H2,H3); simpl in *; auto.
  subst l'.
  apply Permutation_cons_app.
  inversion_clear H.
  apply IHl; auto.
  apply NoDup_remove_1 with a; auto.
  intro x; split; intros.
  assert (In x (l'1++a::l'2)).
   destruct (H1 x); simpl in *; auto.
  apply in_or_app; destruct (in_app_or _ _ _ H4); auto.
  destruct H5; auto.
  subst x; destruct H2; auto.
  assert (In x (l'1++a::l'2)).
    apply in_or_app; destruct (in_app_or _ _ _ H); simpl; auto.
  destruct (H1 x) as (_,H5); destruct H5; auto.
  subst x.
  destruct (NoDup_remove_2 _ _ _ H0 H).
Qed.

End Permutation_properties.

Section Permutation_map.

Variable A B : Type.
Variable f : A -> B.

Add Parametric Morphism : (map f)
  with signature (@Permutation A) ==> (@Permutation B) as Permutation_map_aux.
Proof.
  induction 1; simpl; eauto using Permutation.
Qed.

Lemma Permutation_map :
  forall l l', Permutation l l' -> Permutation (map f l) (map f l').
Proof.
  exact Permutation_map_aux_Proper.
Qed.

End Permutation_map.

(* begin hide *)
Notation Permutation_app_swap := Permutation_app_comm (only parsing).
(* end hide *)
