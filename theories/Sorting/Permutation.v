(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

Require Import List Setoid Compare_dec Morphisms FinFun.
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

Local Hint Constructors Permutation.

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

Instance Permutation_cons A :
 Proper (Logic.eq ==> @Permutation A ==> @Permutation A) (@cons A) | 10.
Proof.
  repeat intro; subst; auto using perm_skip.
Qed.

Section Permutation_properties.

Variable A:Type.

Implicit Types a b : A.
Implicit Types l m : list A.

(** Compatibility with others operations on lists *)

Theorem Permutation_in : forall (l l' : list A) (x : A),
 Permutation l l' -> In x l -> In x l'.
Proof.
  intros l l' x Hperm; induction Hperm; simpl; tauto.
Qed.

Global Instance Permutation_in' :
 Proper (Logic.eq ==> @Permutation A ==> iff) (@In A) | 10.
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
  apply Permutation_trans with (l' := (x :: y :: l ++ m));
   [idtac | repeat rewrite app_comm_cons; apply Permutation_app_head]; trivial.
  apply Permutation_trans with (l' := (l' ++ m')); try assumption.
  apply Permutation_app_tail; assumption.
Qed.

Global Instance Permutation_app' :
 Proper (@Permutation A ==> @Permutation A ==> @Permutation A) (@app A) | 10.
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
Local Hint Resolve Permutation_cons_append.

Theorem Permutation_app_comm : forall (l l' : list A),
  Permutation (l ++ l') (l' ++ l).
Proof.
  induction l as [|x l]; simpl; intro l'.
  rewrite app_nil_r; trivial. rewrite IHl.
  rewrite app_comm_cons, Permutation_cons_append.
  now rewrite <- app_assoc.
Qed.
Local Hint Resolve Permutation_app_comm.

Theorem Permutation_cons_app : forall (l l1 l2:list A) a,
  Permutation l (l1 ++ l2) -> Permutation (a :: l) (l1 ++ a :: l2).
Proof.
  intros l l1 l2 a H. rewrite H.
  rewrite app_comm_cons, Permutation_cons_append.
  now rewrite <- app_assoc.
Qed.
Local Hint Resolve Permutation_cons_app.

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
Local Hint Resolve Permutation_middle.

Theorem Permutation_rev : forall (l : list A), Permutation l (rev l).
Proof.
  induction l as [| x l]; simpl; trivial. now rewrite IHl at 1.
Qed.

Global Instance Permutation_rev' :
 Proper (@Permutation A ==> @Permutation A) (@rev A) | 10.
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

Lemma Permutation_length_1_inv: forall a l, Permutation [a] l -> l = [a].
Proof.
  intros a l H; remember [a] as m in H.
  induction H; try (injection Heqm as -> ->);
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
  induction H; intros; try (injection Heqm as ? ?; subst);
    discriminate || (try tauto).
  apply Permutation_length_1_inv in H as ->; left; auto.
  apply IHPermutation1 in Heqm as [H1|H1]; apply IHPermutation2 in H1 as [];
    auto.
Qed.

Lemma Permutation_length_2 :
  forall a1 a2 b1 b2, Permutation [a1;a2] [b1;b2] ->
    a1 = b1 /\ a2 = b2 \/ a1 = b2 /\ a2 = b1.
Proof.
  intros a1 b1 a2 b2 H.
  apply Permutation_length_2_inv in H as [H|H]; injection H as -> ->; auto.
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

Lemma NoDup_Permutation_bis l l' : NoDup l -> NoDup l' ->
  length l' <= length l -> incl l l' -> Permutation l l'.
Proof.
 intros. apply NoDup_Permutation; auto.
 split; auto. apply NoDup_length_incl; trivial.
Qed.

Lemma Permutation_NoDup l l' : Permutation l l' -> NoDup l -> NoDup l'.
Proof.
 induction 1; auto.
 * inversion_clear 1; constructor; eauto using Permutation_in.
 * inversion_clear 1 as [|? ? H1 H2]. inversion_clear H2; simpl in *.
   constructor. simpl; intuition. constructor; intuition.
Qed.

Global Instance Permutation_NoDup' :
 Proper (@Permutation A ==> iff) (@NoDup A) | 10.
Proof.
  repeat red; eauto using Permutation_NoDup.
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
  Proper (@Permutation A ==> @Permutation B) (map f) | 10.
Proof.
  exact Permutation_map.
Qed.

End Permutation_map.

Lemma nat_bijection_Permutation n f :
 bFun n f ->
 Injective f ->
 let l := seq 0 n in Permutation (map f l) l.
Proof.
 intros Hf BD.
 apply NoDup_Permutation_bis; auto using Injective_map_NoDup, seq_NoDup.
 * now rewrite map_length.
 * intros x. rewrite in_map_iff. intros (y & <- & Hy').
   rewrite in_seq in *. simpl in *.
   destruct Hy' as (_,Hy'). auto with arith.
Qed.

Section Permutation_alt.
Variable A:Type.
Implicit Type a : A.
Implicit Type l : list A.

(** Alternative characterization of permutation
    via [nth_error] and [nth] *)

Let adapt f n :=
 let m := f (S n) in if le_lt_dec m (f 0) then m else pred m.

Let adapt_injective f : Injective f -> Injective (adapt f).
Proof.
 unfold adapt. intros Hf x y EQ.
 destruct le_lt_dec as [LE|LT]; destruct le_lt_dec as [LE'|LT'].
 - now apply eq_add_S, Hf.
 - apply Lt.le_lt_or_eq in LE.
   destruct LE as [LT|EQ']; [|now apply Hf in EQ'].
   unfold lt in LT. rewrite EQ in LT.
   rewrite <- (Lt.S_pred _ _ LT') in LT.
   elim (Lt.lt_not_le _ _ LT' LT).
 - apply Lt.le_lt_or_eq in LE'.
   destruct LE' as [LT'|EQ']; [|now apply Hf in EQ'].
   unfold lt in LT'. rewrite <- EQ in LT'.
   rewrite <- (Lt.S_pred _ _ LT) in LT'.
   elim (Lt.lt_not_le _ _ LT LT').
 - apply eq_add_S, Hf.
   now rewrite (Lt.S_pred _ _ LT), (Lt.S_pred _ _ LT'), EQ.
Qed.

Let adapt_ok a l1 l2 f : Injective f -> length l1 = f 0 ->
 forall n, nth_error (l1++a::l2) (f (S n)) = nth_error (l1++l2) (adapt f n).
Proof.
 unfold adapt. intros Hf E n.
 destruct le_lt_dec as [LE|LT].
 - apply Lt.le_lt_or_eq in LE.
   destruct LE as [LT|EQ]; [|now apply Hf in EQ].
   rewrite <- E in LT.
   rewrite 2 nth_error_app1; auto.
 - rewrite (Lt.S_pred _ _ LT) at 1.
   rewrite <- E, (Lt.S_pred _ _ LT) in LT.
   rewrite 2 nth_error_app2; auto with arith.
   rewrite <- Minus.minus_Sn_m; auto with arith.
Qed.

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
     * revert E. rewrite L12, !app_length. simpl.
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
   destruct (Lt.le_or_lt (length l) (f n)) as [LE|LT]; trivial.
   rewrite <- nth_error_None, <- Hf', nth_error_None, <- E in LE.
   elim (Lt.lt_not_le _ _ Hn LE).
 - intros (f & Hf & Hf2 & Hf3); split; [|exists f; auto].
   assert (H : length l' <= length l') by auto with arith.
   rewrite <- nth_error_None, Hf3, nth_error_None in H.
   destruct (Lt.le_or_lt (length l) (length l')) as [LE|LT];
    [|apply Hf2 in LT; elim (Lt.lt_not_le _ _ LT H)].
   apply Lt.le_lt_or_eq in LE. destruct LE as [LT|EQ]; trivial.
   rewrite <- nth_error_Some, Hf3, nth_error_Some in LT.
   assert (Hf' : bInjective (length l) f).
   { intros x y _ _ E. now apply Hf. }
   rewrite (bInjective_bSurjective Hf2) in Hf'.
   destruct (Hf' _ LT) as (y & Hy & Hy').
   apply Hf in Hy'. subst y. elim (Lt.lt_irrefl _ Hy).
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
   intros x y _ _ Hxy. now apply Hf.
   intros n Hn. rewrite <- 2 nth_default_eq. unfold nth_default.
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
       elim (Lt.lt_irrefl (f y)). eapply Lt.lt_le_trans; eauto.
     + apply Hf1 in LT. intros <-.
       elim (Lt.lt_irrefl (f x)). eapply Lt.lt_le_trans; eauto.
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

(* begin hide *)
Notation Permutation_app_swap := Permutation_app_comm (only parsing).
(* end hide *)
