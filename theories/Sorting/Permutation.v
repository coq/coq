(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*********************************************************************)
(** * List permutations as a composition of adjacent transpositions  *)
(*********************************************************************)

(* Adapted in May 2006 by Jean-Marc Notin from initial contents by
   Laurent Théry (Huffmann contribution, October 2003) *)

Require Import List Setoid Compare_dec Morphisms FinFun PeanoNat.
Import ListNotations. (* For notations [] and [a;b;c] *)
Set Implicit Arguments.
(* Set Universe Polymorphism. *)

Section Permutation.

Variable A:Type.

Inductive Permutation : list A -> list A -> Prop :=
| perm_nil: Permutation [] []
| perm_skip x l l' : Permutation l l' -> Permutation (x::l) (x::l')
| perm_swap x y l : Permutation (y::x::l) (x::y::l)
| perm_trans l l' l'' :
    Permutation l l' -> Permutation l' l'' -> Permutation l l''.

Local Hint Constructors Permutation : core.

(** Some facts about [Permutation] *)

Theorem Permutation_nil : forall (l : list A), Permutation [] l -> l = [].
Proof.
  intros l HF.
  remember (@nil A) as m in HF.
  induction HF; discriminate || auto.
Qed.

Theorem Permutation_nil_cons : forall (l : list A) (x : A),
 ~ Permutation nil (x::l).
Proof.
  intros l x HF.
  apply Permutation_nil in HF; discriminate.
Qed.

(** Permutation over lists is a equivalence relation *)

Theorem Permutation_refl : forall l : list A, Permutation l l.
Proof.
  induction l; constructor. exact IHl.
Qed.

Instance Permutation_refl' : Proper (Logic.eq ==> Permutation) id.
Proof.
  intros x y Heq; rewrite Heq; apply Permutation_refl.
Qed.

Theorem Permutation_sym : forall l l' : list A,
 Permutation l l' -> Permutation l' l.
Proof.
  intros l l' Hperm; induction Hperm; auto.
  apply perm_trans with (l':=l'); assumption.
Qed.

Theorem Permutation_trans : forall l l' l'' : list A,
 Permutation l l' -> Permutation l' l'' -> Permutation l l''.
Proof.
  exact perm_trans.
Qed.

End Permutation.

#[global]
Hint Resolve Permutation_refl perm_nil perm_skip : core.

(* These hints do not reduce the size of the problem to solve and they
   must be used with care to avoid combinatoric explosions *)

Local Hint Resolve perm_swap perm_trans : core.
Local Hint Resolve Permutation_sym Permutation_trans : core.

(* This provides reflexivity, symmetry and transitivity and rewriting
   on morphims to come *)

#[global]
Instance Permutation_Equivalence A : Equivalence (@Permutation A) := {
  Equivalence_Reflexive := @Permutation_refl A ;
  Equivalence_Symmetric := @Permutation_sym A ;
  Equivalence_Transitive := @Permutation_trans A }.

Lemma Permutation_morph_transp A : forall P : list A -> Prop,
 (forall a b l1 l2, P (l1 ++ a :: b :: l2) -> P (l1 ++ b :: a :: l2)) ->
 Proper (@Permutation A ==> Basics.impl) P.
Proof.
  intros P HT l1 l2 HP.
  enough (forall l0, P (l0 ++ l1) -> P (l0 ++ l2)) as IH
    by (intro; rewrite <- (app_nil_l l2); now apply (IH nil)).
  induction HP; intuition.
  rewrite <- (app_nil_l l'), app_comm_cons, app_assoc.
  now apply IHHP; rewrite <- app_assoc.
Qed.

#[export]
Instance Permutation_cons A :
 Proper (Logic.eq ==> @Permutation A ==> @Permutation A) (@cons A).
Proof.
  repeat intro; subst; auto using perm_skip.
Qed.


Section Permutation_properties.

Variable A B:Type.

Implicit Types a : A.
Implicit Types l m : list A.

(** Compatibility with others operations on lists *)

Theorem Permutation_in : forall (l l' : list A) (x : A),
 Permutation l l' -> In x l -> In x l'.
Proof.
  intros l l' x Hperm; induction Hperm; simpl; tauto.
Qed.

Global Instance Permutation_in' :
 Proper (Logic.eq ==> @Permutation A ==> iff) (@In A).
Proof.
  repeat red; intros; subst; eauto using Permutation_in.
Qed.

Lemma Permutation_app_tail : forall (l l' tl : list A),
 Permutation l l' -> Permutation (l++tl) (l'++tl).
Proof.
  intros l l' tl Hperm; induction Hperm as [|x l l'|x y l|l l' l'']; simpl; auto.
  eapply Permutation_trans with (l':=l'++tl); trivial.
Qed.

Lemma Permutation_app_head : forall (l tl tl' : list A),
 Permutation tl tl' -> Permutation (l++tl) (l++tl').
Proof.
  intros l tl tl' Hperm; induction l;
   [trivial | repeat rewrite <- app_comm_cons; constructor; assumption].
Qed.

Theorem Permutation_app : forall (l m l' m' : list A),
 Permutation l l' -> Permutation m m' -> Permutation (l++m) (l'++m').
Proof.
  intros l m l' m' Hpermll' Hpermmm';
   induction Hpermll' as [|x l l'|x y l|l l' l''];
    repeat rewrite <- app_comm_cons; auto.
  - apply Permutation_trans with (l' := (x :: y :: l ++ m));
      [idtac | repeat rewrite app_comm_cons; apply Permutation_app_head]; trivial.
  - apply Permutation_trans with (l' := (l' ++ m')); try assumption.
    apply Permutation_app_tail; assumption.
Qed.

#[export] Instance Permutation_app' :
 Proper (@Permutation A ==> @Permutation A ==> @Permutation A) (@app A).
Proof.
  repeat intro; now apply Permutation_app.
Qed.

Lemma Permutation_add_inside : forall a (l l' tl tl' : list A),
  Permutation l l' -> Permutation tl tl' ->
  Permutation (l ++ a :: tl) (l' ++ a :: tl').
Proof.
  intros; apply Permutation_app; auto.
Qed.

Lemma Permutation_cons_append : forall (l : list A) x,
  Permutation (x :: l) (l ++ x :: nil).
Proof. induction l; intros; auto. simpl. rewrite <- IHl; auto. Qed.
Local Hint Resolve Permutation_cons_append : core.

Theorem Permutation_app_comm : forall (l l' : list A),
  Permutation (l ++ l') (l' ++ l).
Proof.
  induction l as [|x l]; simpl; intro l'.
  - rewrite app_nil_r; trivial.
  - rewrite IHl.
    rewrite app_comm_cons, Permutation_cons_append.
    now rewrite <- app_assoc.
Qed.
Local Hint Resolve Permutation_app_comm : core.

Lemma Permutation_app_rot : forall l1 l2 l3: list A,
  Permutation (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
Proof.
  intros l1 l2 l3; now rewrite (app_assoc l2).
Qed.
Local Hint Resolve Permutation_app_rot : core.

Lemma Permutation_app_swap_app : forall l1 l2 l3: list A,
  Permutation (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
Proof.
  intros.
  rewrite 2 app_assoc.
  apply Permutation_app_tail, Permutation_app_comm.
Qed.
Local Hint Resolve Permutation_app_swap_app : core.

Lemma Permutation_app_middle : forall l l1 l2 l3 l4,
 Permutation (l1 ++ l2) (l3 ++ l4) ->
 Permutation (l1 ++ l ++ l2) (l3 ++ l ++ l4).
Proof.
  intros l l1 l2 l3 l4 HP.
  now rewrite Permutation_app_swap_app, HP, Permutation_app_swap_app.
Qed.

Theorem Permutation_cons_app : forall (l l1 l2:list A) a,
  Permutation l (l1 ++ l2) -> Permutation (a :: l) (l1 ++ a :: l2).
Proof.
  intros l l1 l2 a H. rewrite H.
  rewrite app_comm_cons, Permutation_cons_append.
  now rewrite <- app_assoc.
Qed.
Local Hint Resolve Permutation_cons_app : core.

Lemma Permutation_Add a l l' : Add a l l' -> Permutation (a::l) l'.
Proof.
 induction 1; simpl; trivial.
 rewrite perm_swap. now apply perm_skip.
Qed.

Theorem Permutation_middle : forall (l1 l2:list A) a,
  Permutation (a :: l1 ++ l2) (l1 ++ a :: l2).
Proof.
  auto.
Qed.
Local Hint Resolve Permutation_middle : core.

Lemma Permutation_middle2 : forall l1 l2 l3 a b,
  Permutation (a :: b :: l1 ++ l2 ++ l3) (l1 ++ a :: l2 ++ b :: l3).
Proof.
  intros l1 l2 l3 a b.
  apply Permutation_cons_app.
  rewrite 2 app_assoc.
  now apply Permutation_cons_app.
Qed.
Local Hint Resolve Permutation_middle2 : core.

Lemma Permutation_elt : forall l1 l2 l1' l2' (a:A),
 Permutation (l1 ++ l2) (l1' ++ l2') ->
 Permutation (l1 ++ a :: l2) (l1' ++ a :: l2').
Proof.
  intros l1 l2 l1' l2' a HP.
  transitivity (a :: l1 ++ l2); auto.
Qed.

Theorem Permutation_rev : forall (l : list A), Permutation l (rev l).
Proof.
  induction l as [| x l]; simpl; trivial. now rewrite IHl at 1.
Qed.

Global Instance Permutation_rev' :
 Proper (@Permutation A ==> @Permutation A) (@rev A).
Proof.
  repeat intro; now rewrite <- 2 Permutation_rev.
Qed.

Theorem Permutation_length : forall (l l' : list A),
 Permutation l l' -> length l = length l'.
Proof.
  intros l l' Hperm; induction Hperm; simpl; auto. now transitivity (length l').
Qed.

Global Instance Permutation_length' :
 Proper (@Permutation A ==> Logic.eq) (@length A) | 10.
Proof.
  exact Permutation_length.
Qed.

Global Instance Permutation_Forall (P : A -> Prop) :
 Proper ((@Permutation A) ==> Basics.impl) (Forall P).
Proof.
  intros l1 l2 HP.
  induction HP; intro HF; auto.
  - inversion_clear HF; auto.
  - inversion_clear HF as [ | ? ? HF1 HF2].
    inversion_clear HF2; auto.
Qed.

Global Instance Permutation_Exists (P : A -> Prop) :
 Proper ((@Permutation A) ==> Basics.impl) (Exists P).
Proof.
  intros l1 l2 HP.
  induction HP; intro HF; auto.
  - inversion_clear HF; auto.
  - inversion_clear HF as [ | ? ? HF1 ]; auto.
    inversion_clear HF1; auto.
Qed.

Lemma Permutation_Forall2 (P : A -> B -> Prop) :
 forall l1 l1' (l2 : list B), Permutation l1 l1' -> Forall2 P l1 l2 ->
 exists l2' : list B, Permutation l2 l2' /\ Forall2 P l1' l2'.
Proof.
  intros l1 l1' l2 HP.
  revert l2; induction HP; intros l2 HF; inversion HF as [ | ? b ? ? HF1 HF2 ]; subst.
  - now exists nil.
  - apply IHHP in HF2 as [l2' [HP2 HF2]].
    exists (b :: l2'); auto.
  - inversion_clear HF2 as [ | ? b' ? l2' HF3 HF4 ].
    exists (b' :: b :: l2'); auto.
  - apply Permutation_nil in HP1; subst.
    apply Permutation_nil in HP2; subst.
    now exists nil.
  - apply IHHP1 in HF as [l2' [HP2' HF2']].
    apply IHHP2 in HF2' as [l2'' [HP2'' HF2'']].
    exists l2''; split; auto.
    now transitivity l2'.
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
  - apply Htrans with (x::y::l); auto.
    + apply Hswap; auto.
      induction l; auto.
    + apply Hskip; auto.
      apply Hskip; auto.
      induction l; auto.
  - eauto.
Qed.

Theorem Permutation_nil_app_cons : forall (l l' : list A) (x : A),
 ~ Permutation nil (l++x::l').
Proof.
  intros l l' x HF.
  apply Permutation_nil in HF. destruct l; discriminate.
Qed.

Ltac InvAdd := repeat (match goal with
 | H: Add ?x _ (_ :: _) |- _ => inversion H; clear H; subst
 end).

Ltac finish_basic_perms H :=
  try constructor; try rewrite perm_swap; try constructor; trivial;
  (rewrite <- H; now apply Permutation_Add) ||
  (rewrite H; symmetry; now apply Permutation_Add).

Theorem Permutation_Add_inv a l1 l2 :
  Permutation l1 l2 -> forall l1' l2', Add a l1' l1 -> Add a l2' l2 ->
   Permutation l1' l2'.
Proof.
 revert l1 l2. refine (Permutation_ind_bis _ _ _ _ _).
 - (* nil *)
   inversion_clear 1.
 - (* skip *)
   intros x l1 l2 PE IH. intros. InvAdd; try finish_basic_perms PE.
   constructor. now apply IH.
 - (* swap *)
   intros x y l1 l2 PE IH. intros. InvAdd; try finish_basic_perms PE.
   rewrite perm_swap; do 2 constructor. now apply IH.
 - (* trans *)
   intros l1 l l2 PE IH PE' IH' l1' l2' AD1 AD2.
   assert (Ha : In a l). { rewrite <- PE. rewrite (Add_in AD1). simpl; auto. }
   destruct (Add_inv _ _ Ha) as (l',AD).
   transitivity l'; auto.
Qed.

Theorem Permutation_app_inv (l1 l2 l3 l4:list A) a :
  Permutation (l1++a::l2) (l3++a::l4) -> Permutation (l1++l2) (l3 ++ l4).
Proof.
 intros. eapply Permutation_Add_inv; eauto using Add_app.
Qed.

Theorem Permutation_cons_inv l l' a :
 Permutation (a::l) (a::l') -> Permutation l l'.
Proof.
  intro. eapply Permutation_Add_inv; eauto using Add_head.
Qed.

Theorem Permutation_cons_app_inv l l1 l2 a :
 Permutation (a :: l) (l1 ++ a :: l2) -> Permutation l (l1 ++ l2).
Proof.
  intro. eapply Permutation_Add_inv; eauto using Add_head, Add_app.
Qed.

Theorem Permutation_app_inv_l : forall l l1 l2,
 Permutation (l ++ l1) (l ++ l2) -> Permutation l1 l2.
Proof.
  induction l; simpl; auto.
  intros.
  apply IHl.
  apply Permutation_cons_inv with a; auto.
Qed.

Theorem Permutation_app_inv_r l l1 l2 :
 Permutation (l1 ++ l) (l2 ++ l) -> Permutation l1 l2.
Proof.
 rewrite 2 (Permutation_app_comm _ l). apply Permutation_app_inv_l.
Qed.

Lemma Permutation_app_inv_m l l1 l2 l3 l4 :
 Permutation (l1 ++ l ++ l2) (l3 ++ l ++ l4) ->
 Permutation (l1 ++ l2) (l3 ++ l4).
Proof.
  intros HP.
  apply (Permutation_app_inv_l l).
  transitivity (l1 ++ l ++ l2); auto.
  transitivity (l3 ++ l ++ l4); auto.
Qed.

Lemma Permutation_length_1_inv: forall a l, Permutation [a] l -> l = [a].
Proof.
  intros a l H; remember [a] as m in H.
  induction H; try (injection Heqm as [= -> ->]);
    discriminate || auto.
  apply Permutation_nil in H as ->; trivial.
Qed.

Lemma Permutation_length_1: forall a b, Permutation [a] [b] -> a = b.
Proof.
  intros a b H.
  apply Permutation_length_1_inv in H; injection H as [= ->]; trivial.
Qed.

Lemma Permutation_length_2_inv :
  forall a1 a2 l, Permutation [a1;a2] l -> l = [a1;a2] \/ l = [a2;a1].
Proof.
  intros a1 a2 l H; remember [a1;a2] as m in H.
  revert a1 a2 Heqm.
  induction H; intros; try (injection Heqm as [= ? ?]; subst);
    discriminate || (try tauto).
  - apply Permutation_length_1_inv in H as ->; left; auto.
  - apply IHPermutation1 in Heqm as [H1|H1]; apply IHPermutation2 in H1 as [];
      auto.
Qed.

Lemma Permutation_length_2 :
  forall a1 a2 b1 b2, Permutation [a1;a2] [b1;b2] ->
    a1 = b1 /\ a2 = b2 \/ a1 = b2 /\ a2 = b1.
Proof.
  intros a1 b1 a2 b2 H.
  apply Permutation_length_2_inv in H as [H|H]; injection H as [= -> ->]; auto.
Qed.

Lemma Permutation_vs_elt_inv : forall l l1 l2 a,
 Permutation l (l1 ++ a :: l2) -> exists l' l'', l = l' ++ a :: l''.
Proof.
  intros l l1 l2 a HP.
  symmetry in HP.
  apply (Permutation_in a), in_split in HP; trivial.
  apply in_elt.
Qed.

Lemma Permutation_vs_cons_inv : forall l l1 a,
  Permutation l (a :: l1) -> exists l' l'', l = l' ++ a :: l''.
Proof.
  intros l l1 a HP.
  rewrite <- (app_nil_l (a :: l1)) in HP.
  apply (Permutation_vs_elt_inv _ _ _ HP).
Qed.

Lemma Permutation_vs_cons_cons_inv : forall l l' a b,
 Permutation l (a :: b :: l') ->
 exists l1 l2 l3, l = l1 ++ a :: l2 ++ b :: l3 \/ l = l1 ++ b :: l2 ++ a :: l3.
Proof.
  intros l l' a b HP.
  destruct (Permutation_vs_cons_inv HP) as [l1 [l2]]; subst.
  symmetry in HP.
  apply Permutation_cons_app_inv in HP.
  apply (Permutation_in b), in_app_or in HP; [|now apply in_eq].
  destruct HP as [(l3 & l4 & ->)%in_split | (l3 & l4 & ->)%in_split].
  - exists l3, l4, l2; right.
    now rewrite <-app_assoc; simpl.
  - now exists l1, l3, l4; left.
Qed.

Lemma NoDup_Permutation l l' : NoDup l -> NoDup l' ->
  (forall x:A, In x l <-> In x l') -> Permutation l l'.
Proof.
 intros N. revert l'. induction N as [|a l Hal Hl IH].
 - destruct l'; simpl; auto.
   intros Hl' H. exfalso. rewrite (H a); auto.
 - intros l' Hl' H.
   assert (Ha : In a l') by (apply H; simpl; auto).
   destruct (Add_inv _ _ Ha) as (l'' & AD).
   rewrite <- (Permutation_Add AD).
   apply perm_skip.
   apply IH; clear IH.
   * now apply (NoDup_Add AD).
   * split.
     + apply incl_Add_inv with a l'; trivial. intro. apply H.
     + intro Hx.
       assert (Hx' : In x (a::l)).
       { apply H. rewrite (Add_in AD). now right. }
       destruct Hx'; simpl; trivial. subst.
       rewrite (NoDup_Add AD) in Hl'. tauto.
Qed.

Lemma NoDup_Permutation_bis l l' : NoDup l ->
  length l' <= length l -> incl l l' -> Permutation l l'.
Proof.
 intros. apply NoDup_Permutation; auto.
 - now apply NoDup_incl_NoDup with l.
 - split; auto.
   apply NoDup_length_incl; trivial.
Qed.

Lemma Permutation_NoDup l l' : Permutation l l' -> NoDup l -> NoDup l'.
Proof.
 induction 1; auto.
 - inversion_clear 1; constructor; eauto using Permutation_in.
 - inversion_clear 1 as [|? ? H1 H2]. inversion_clear H2; simpl in *.
   constructor.
   + simpl; intuition.
   + constructor; intuition.
Qed.

Global Instance Permutation_NoDup' :
 Proper (@Permutation A ==> iff) (@NoDup A).
Proof.
  repeat red; eauto using Permutation_NoDup.
Qed.

Lemma Permutation_repeat x n l :
  Permutation l (repeat x n) -> l = repeat x n.
Proof.
  revert n; induction l as [|y l IHl] ; simpl; intros n HP; auto.
  - now apply Permutation_nil in HP; inversion HP.
  - assert (y = x) as Heq by (now apply repeat_spec with n, (Permutation_in _ HP); left); subst.
    destruct n; simpl; simpl in HP.
    + symmetry in HP; apply Permutation_nil in HP; inversion HP.
    + f_equal; apply IHl.
      now apply Permutation_cons_inv with x.
Qed.

Lemma Permutation_incl_cons_inv_r (l1 l2 : list A) a : incl l1 (a :: l2) ->
  exists n l3, Permutation l1 (repeat a n ++ l3) /\ incl l3 l2.
Proof.
  induction l1 as [|b l1 IH].
  - intros _. now exists 0, nil.
  - intros [Hb Hincl] %incl_cons_inv.
    destruct (IH Hincl) as [n [l3 [Hl1 Hl3l2]]].
    destruct Hb.
    + subst b. exists (S n), l3. eauto.
    + exists n, (b :: l3). eauto using incl_cons.
Qed.

Lemma Permutation_pigeonhole l1 l2 : incl l1 l2 -> length l2 < length l1 ->
  exists a l3, Permutation l1 (a :: a :: l3).
Proof.
  induction l2 as [|a l2 IH] in l1 |- *.
  - intros -> %incl_l_nil [] %PeanoNat.Nat.nlt_0_r.
  - intros [[|[|n]] [l4 [Hl1 Hl4]]] %Permutation_incl_cons_inv_r Hlen.
    + apply IH.
      * unfold incl. eauto using Permutation_in.
      * eauto using PeanoNat.Nat.lt_trans.
    + assert (Hl2l4 : length l2 < length l4).
      { rewrite (Permutation_length Hl1) in Hlen.
        now apply PeanoNat.Nat.succ_lt_mono. }
      destruct (IH l4 Hl4 Hl2l4) as [b [l3 Hl4l3]].
      exists b, (a :: l3).
      apply (Permutation_trans Hl1).
      now apply (Permutation_cons_app (b :: b :: nil)).
    + now exists a, (repeat a n ++ l4).
Qed.

Lemma Permutation_pigeonhole_rel (R : B -> A -> Prop) (l1 : list B) l2 :
  Forall (fun b => Exists (R b) l2) l1 ->
  length l2 < length l1 ->
  exists b b' (l3 : list B), Permutation l1 (b :: b' :: l3) /\ exists a, In a l2 /\ R b a /\ R b' a.
Proof.
  intros [l2' [Hl2'l1 Hl2'l2]]%Forall_Exists_exists_Forall2.
  intros Hl2l2'. rewrite (Forall2_length Hl2'l1) in Hl2l2'.
  destruct (Permutation_pigeonhole Hl2'l2 Hl2l2') as [a [l3 Hl2']].
  destruct (Permutation_Forall2 Hl2' (Forall2_flip Hl2'l1)) as [l1' [Hl1l1' Hl1']].
  destruct (Forall2_app_inv_l [a; a] l3 Hl1') as [lbb' [l1'' [Ha [? ?]]]].
  assert (Hlbb' := Forall2_length Ha).
  destruct lbb' as [|b lb']; [easy|].
  apply Forall2_cons_iff in Ha as [Hba Ha].
  destruct lb' as [|b' l]; [easy|].
  apply Forall2_cons_iff in Ha as [Hb'a Ha].
  inversion Ha. subst. exists b, b', l1''.
  split; [easy|]. exists a.
  split; eauto using Permutation_in, in_eq.
Qed.

Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

Lemma Permutation_count_occ l1 l2 :
  Permutation l1 l2 <-> forall x, count_occ eq_dec l1 x = count_occ eq_dec l2 x.
Proof.
  split.
  - induction 1 as [ | y l1 l2 HP IHP | y z l | l1 l2 l3 HP1 IHP1 HP2 IHP2 ];
      cbn; intros a; auto.
    + now rewrite IHP.
    + destruct (eq_dec y a); destruct (eq_dec z a); auto.
    + now rewrite IHP1, IHP2.
  - revert l2; induction l1 as [|y l1 IHl1]; cbn; intros l2 Hocc.
    + replace l2 with (@nil A); auto.
      symmetry; apply (count_occ_inv_nil eq_dec); intuition.
    + assert (exists l2' l2'', l2 = l2' ++ y :: l2'') as [l2' [l2'' ->]].
      { specialize (Hocc y).
        destruct (eq_dec y y); intuition.
        apply in_split, (count_occ_In eq_dec).
        rewrite <- Hocc; apply Nat.lt_0_succ. }
      apply Permutation_cons_app, IHl1.
      intros z; specialize (Hocc z); destruct (eq_dec y z) as [Heq | Hneq].
      * rewrite (count_occ_elt_eq _ _ _ Heq) in Hocc.
        now injection Hocc.
      * now rewrite (count_occ_elt_neq _ _ _ Hneq) in Hocc.
Qed.

End Permutation_properties.

Section Permutation_map.

Variable A B : Type.
Variable f : A -> B.

Lemma Permutation_map l l' :
  Permutation l l' -> Permutation (map f l) (map f l').
Proof.
 induction 1; simpl; eauto.
Qed.

Global Instance Permutation_map' :
  Proper (@Permutation A ==> @Permutation B) (map f).
Proof.
  exact Permutation_map.
Qed.

Lemma Permutation_map_inv : forall l1 l2,
 Permutation l1 (map f l2) -> exists l3, l1 = map f l3 /\ Permutation l2 l3.
Proof.
  induction l1; intros l2 HP.
  - exists nil; split; auto.
    apply Permutation_nil in HP.
    destruct l2; auto.
    inversion HP.
  - symmetry in HP.
    destruct (Permutation_vs_cons_inv HP) as [l3 [l4 Heq]].
    destruct (map_eq_app _ _ _ _ Heq) as [l1' [l2' [Heq1 [Heq2 Heq3]]]]; subst.
    destruct (map_eq_cons _ _ Heq3) as [b [l1'' [Heq1' [Heq2' Heq3']]]]; subst.
    rewrite map_app in HP; simpl in HP.
    symmetry in HP.
    apply Permutation_cons_app_inv in HP.
    rewrite <- map_app in HP.
    destruct (IHl1 _ HP) as [l3 [Heq1'' Heq2'']]; subst.
    exists (b :: l3); split; auto.
    symmetry in Heq2''; symmetry; apply (Permutation_cons_app _ _ _ Heq2'').
Qed.

Lemma Permutation_image : forall a l l',
 Permutation (a :: l) (map f l') -> exists a', a = f a'.
Proof.
  intros a l l' HP.
  destruct (Permutation_map_inv _ HP) as [l'' [Heq _]].
  destruct l'' as [ | a' l'']; inversion_clear Heq.
  now exists a'.
Qed.

Lemma Permutation_elt_map_inv: forall l1 l2 l3 l4 a,
 Permutation (l1 ++ a :: l2) (l3 ++ map f l4) -> (forall b, a <> f b) ->
 exists l1' l2', l3 = l1' ++ a :: l2'.
Proof.
  intros l1 l2 l3 l4 a HP Hf.
  apply (Permutation_in a), in_app_or in HP; [| now apply in_elt].
  destruct HP as [HP%in_split | (x & Heq & ?)%in_map_iff]; trivial; subst.
  now contradiction (Hf x).
Qed.

Global Instance Permutation_flat_map (g : A -> list B) :
 Proper ((@Permutation A) ==> (@Permutation B)) (flat_map g).
Proof.
  intros l1; induction l1; intros l2 HP.
  - now apply Permutation_nil in HP; subst.
  - symmetry in HP.
    destruct (Permutation_vs_cons_inv HP) as [l' [l'']]; subst.
    symmetry in HP.
    apply Permutation_cons_app_inv in HP.
    rewrite flat_map_app; simpl.
    rewrite <- (app_nil_l _).
    apply Permutation_app_middle; simpl.
    rewrite <- flat_map_app.
    apply (IHl1 _ HP).
Qed.

End Permutation_map.

Lemma Permutation_map_same_l {A} (f : A -> A) (l : list A) :
  List.NoDup (List.map f l) -> List.incl (List.map f l) l -> Permutation (List.map f l) l.
Proof.
  intros; eapply Permutation.NoDup_Permutation_bis; rewrite ?List.length_map; trivial.
Qed.

Lemma nat_bijection_Permutation n f :
 bFun n f ->
 Injective f ->
 let l := seq 0 n in Permutation (map f l) l.
Proof.
 intros Hf BD.
 apply NoDup_Permutation_bis; auto using Injective_map_NoDup, seq_NoDup.
 * now rewrite length_map.
 * intros x. rewrite in_map_iff. intros (y & <- & Hy').
   rewrite in_seq in *. simpl in *.
   destruct Hy' as (_,Hy').
   split; [ apply Nat.le_0_l | auto ].
Qed.

Section Permutation_alt.
Variable A:Type.
Implicit Type a : A.
Implicit Type l : list A.

(** Alternative characterization of permutation
    via [nth_error] and [nth] *)

Let adapt f n :=
 let m := f (S n) in if le_lt_dec m (f 0) then m else pred m.

Local Definition adapt_injective f : Injective f -> Injective (adapt f).
Proof.
 unfold adapt. intros Hf x y EQ.
 destruct le_lt_dec as [LE|LT]; destruct le_lt_dec as [LE'|LT'].
 - now apply eq_add_S, Hf.
 - apply Nat.lt_eq_cases in LE.
   destruct LE as [LT|EQ']; [|now apply Hf in EQ'].
   unfold lt in LT. rewrite EQ in LT.
   rewrite (Nat.lt_succ_pred _ _ LT') in LT.
   elim (proj1 (Nat.lt_nge _ _) LT' LT).
 - apply Nat.lt_eq_cases in LE'.
   destruct LE' as [LT'|EQ']; [|now apply Hf in EQ'].
   unfold lt in LT'. rewrite <- EQ in LT'.
   rewrite (Nat.lt_succ_pred _ _ LT) in LT'.
   elim (proj1 (Nat.lt_nge _ _) LT LT').
 - apply eq_add_S, Hf.
   now rewrite <- (Nat.lt_succ_pred _ _ LT), <- (Nat.lt_succ_pred _ _ LT'), EQ.
Defined.

Local Definition adapt_ok a l1 l2 f : Injective f -> length l1 = f 0 ->
 forall n, nth_error (l1++a::l2) (f (S n)) = nth_error (l1++l2) (adapt f n).
Proof.
 unfold adapt. intros Hf E n.
 destruct le_lt_dec as [LE|LT].
 - apply Nat.lt_eq_cases in LE.
   destruct LE as [LT|EQ]; [|now apply Hf in EQ].
   rewrite <- E in LT.
   rewrite 2 nth_error_app1; auto.
 - rewrite <- (Nat.lt_succ_pred _ _ LT) at 1.
   rewrite <- E, <- (Nat.lt_succ_pred _ _ LT) in LT.
   rewrite 2 nth_error_app2.
   + rewrite Nat.sub_succ_l; [ reflexivity | ].
     apply Nat.lt_succ_r; assumption.
   + apply Nat.lt_succ_r; assumption.
   + apply Nat.lt_le_incl; assumption.
Defined.

Lemma Permutation_nth_error l l' :
 Permutation l l' <->
  (length l = length l' /\
   exists f:nat->nat,
    Injective f /\ forall n, nth_error l' n = nth_error l (f n)).
Proof.
 split.
 { intros P.
   split; [now apply Permutation_length|].
   induction P.
   - exists (fun n => n).
     split; try red; auto.
   - destruct IHP as (f & Hf & Hf').
     exists (fun n => match n with O => O | S n => S (f n) end).
     split; try red.
     * intros [|y] [|z]; simpl; now auto.
     * intros [|n]; simpl; auto.
   - exists (fun n => match n with 0 => 1 | 1 => 0 | n => n end).
     split; try red.
     * intros [|[|z]] [|[|t]]; simpl; now auto.
     * intros [|[|n]]; simpl; auto.
   - destruct IHP1 as (f & Hf & Hf').
     destruct IHP2 as (g & Hg & Hg').
     exists (fun n => f (g n)).
     split; try red.
     * auto.
     * intros n. rewrite <- Hf'; auto. }
 { revert l. induction l'.
   - intros [|l] (E & _); now auto.
   - intros l (E & f & Hf & Hf').
     simpl in E.
     assert (Ha : nth_error l (f 0) = Some a)
      by (symmetry; apply (Hf' 0)).
     destruct (nth_error_split l (f 0) Ha) as (l1 & l2 & L12 & L1).
     rewrite L12. rewrite <- Permutation_middle. constructor.
     apply IHl'; split; [|exists (adapt f); split].
     * revert E. rewrite L12, !length_app. simpl.
       rewrite <- plus_n_Sm. now injection 1.
     * now apply adapt_injective.
     * intro n. rewrite <- (adapt_ok a), <- L12; auto.
       apply (Hf' (S n)). }
Qed.

Lemma Permutation_nth_error_bis l l' :
 Permutation l l' <->
  exists f:nat->nat,
    Injective f /\
    bFun (length l) f /\
    (forall n, nth_error l' n = nth_error l (f n)).
Proof.
 rewrite Permutation_nth_error; split.
 - intros (E & f & Hf & Hf').
   exists f. do 2 (split; trivial).
   intros n Hn.
   destruct (Nat.le_gt_cases (length l) (f n)) as [LE|LT]; trivial.
   rewrite <- nth_error_None, <- Hf', nth_error_None, <- E in LE.
   elim (proj1 (Nat.lt_nge _ _) Hn LE).
 - intros (f & Hf & Hf2 & Hf3); split; [|exists f; auto].
   assert (H : length l' <= length l') by auto.
   rewrite <- nth_error_None, Hf3, nth_error_None in H.
   destruct (Nat.le_gt_cases (length l) (length l')) as [LE|LT];
    [|apply Hf2 in LT; elim (proj1 (Nat.lt_nge _ _) LT H)].
   apply Nat.lt_eq_cases in LE. destruct LE as [LT|EQ]; trivial.
   rewrite <- nth_error_Some, Hf3, nth_error_Some in LT.
   assert (Hf' : bInjective (length l) f).
   { intros x y _ _ E. now apply Hf. }
   rewrite (bInjective_bSurjective Hf2) in Hf'.
   destruct (Hf' _ LT) as (y & Hy & Hy').
   apply Hf in Hy'. subst y. elim (Nat.lt_irrefl _ Hy).
Qed.

Lemma Permutation_nth l l' d :
 Permutation l l' <->
  (let n := length l in
   length l' = n /\
   exists f:nat->nat,
    bFun n f /\
    bInjective n f /\
    (forall x, x < n -> nth x l' d = nth (f x) l d)).
Proof.
 split.
 - intros H.
   assert (E := Permutation_length H).
   split; auto.
   apply Permutation_nth_error_bis in H.
   destruct H as (f & Hf & Hf2 & Hf3).
   exists f. split; [|split]; auto.
   + intros x y _ _ Hxy. now apply Hf.
   + intros n Hn. rewrite <- 2 nth_default_eq. unfold nth_default.
     now rewrite Hf3.
 - intros (E & f & Hf1 & Hf2 & Hf3).
   rewrite Permutation_nth_error.
   split; auto.
   exists (fun n => if le_lt_dec (length l) n then n else f n).
   split.
   * intros x y.
     destruct le_lt_dec as [LE|LT];
      destruct le_lt_dec as [LE'|LT']; auto.
     + apply Hf1 in LT'. intros ->.
       elim (Nat.lt_irrefl (f y)). eapply Nat.lt_le_trans; eauto.
     + apply Hf1 in LT. intros <-.
       elim (Nat.lt_irrefl (f x)). eapply Nat.lt_le_trans; eauto.
   * intros n.
     destruct le_lt_dec as [LE|LT].
     + assert (LE' : length l' <= n) by (now rewrite E).
       rewrite <- nth_error_None in LE, LE'. congruence.
     + assert (LT' : n < length l') by (now rewrite E).
       specialize (Hf3 n LT). rewrite <- 2 nth_default_eq in Hf3.
       unfold nth_default in Hf3.
       apply Hf1 in LT.
       rewrite <- nth_error_Some in LT, LT'.
       do 2 destruct nth_error; congruence.
Qed.

End Permutation_alt.

#[global]
Instance Permutation_list_sum : Proper (@Permutation nat ==> eq) list_sum | 10.
Proof.
  intros l1 l2 HP; induction HP; simpl; intuition.
  - rewrite 2 (Nat.add_comm x).
    apply Nat.add_assoc.
  - now transitivity (list_sum l').
Qed.

#[global]
Instance Permutation_list_max : Proper (@Permutation nat ==> eq) list_max | 10.
Proof.
  intros l1 l2 HP; induction HP; simpl; intuition.
  - rewrite 2 (Nat.max_comm x).
    apply Nat.max_assoc.
  - now transitivity (list_max l').
Qed.

Section Permutation_transp.

Variable A:Type.

(** Permutation definition based on transpositions for induction with fixed length *)
Inductive Permutation_transp : list A -> list A -> Prop :=
| perm_t_refl : forall l, Permutation_transp l l
| perm_t_swap : forall x y l1 l2, Permutation_transp (l1 ++ y :: x :: l2) (l1 ++ x :: y :: l2)
| perm_t_trans l l' l'' :
    Permutation_transp l l' -> Permutation_transp l' l'' -> Permutation_transp l l''.

Instance Permutation_transp_sym : Symmetric Permutation_transp.
Proof.
  intros l1 l2 HP; induction HP; subst; try (now constructor).
  now apply (perm_t_trans IHHP2).
Qed.

Global Instance Permutation_transp_equiv : Equivalence Permutation_transp | 100.
Proof.
  split.
  - intros l; apply perm_t_refl.
  - apply Permutation_transp_sym.
  - intros l1 l2 l3 ;apply perm_t_trans.
Qed.

Lemma Permutation_transp_cons : forall (x : A) l1 l2,
 Permutation_transp l1 l2 -> Permutation_transp (x :: l1) (x :: l2).
Proof.
  intros x l1 l2 HP.
  induction HP.
  - reflexivity.
  - rewrite 2 app_comm_cons.
    apply perm_t_swap.
  - now transitivity (x :: l').
Qed.

Lemma Permutation_Permutation_transp : forall l1 l2 : list A,
 Permutation l1 l2 <-> Permutation_transp l1 l2.
Proof.
  intros l1 l2; split; intros HP; induction HP; intuition auto.
  - solve_relation.
  - now apply Permutation_transp_cons.
  - rewrite <- (app_nil_l (y :: _)).
    rewrite <- (app_nil_l (x :: y :: _)).
    apply perm_t_swap.
  - now transitivity l'.
  - apply Permutation_app_head.
    apply perm_swap.
  - now transitivity l'.
Qed.

Lemma Permutation_ind_transp : forall P : list A -> list A -> Prop,
  (forall l, P l l) ->
  (forall x y l1 l2, P (l1 ++ y :: x :: l2) (l1 ++ x :: y :: l2)) ->
  (forall l l' l'',
     Permutation l l' -> P l l' -> Permutation l' l'' -> P l' l'' -> P l l'') ->
  forall l1 l2, Permutation l1 l2 -> P l1 l2.
Proof.
  intros P Hr Ht Htr l1 l2 HP; apply Permutation_Permutation_transp in HP.
  revert Hr Ht Htr; induction HP; intros Hr Ht Htr; auto.
  apply (Htr _ l'); intuition; now apply Permutation_Permutation_transp.
Qed.

End Permutation_transp.

(* begin hide *)
Notation Permutation_app_swap := Permutation_app_comm (only parsing).
(* end hide *)
