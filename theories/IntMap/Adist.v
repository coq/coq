(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i 	     $Id$	      i*)

Require Import Bool.
Require Import ZArith.
Require Import Arith.
Require Import Min.
Require Import Addr.

Fixpoint ad_plength_1 (p:positive) : nat :=
  match p with
  | xH => 0
  | xI _ => 0
  | xO p' => S (ad_plength_1 p')
  end.

Inductive natinf : Set :=
  | infty : natinf
  | ni : nat -> natinf.

Definition ad_plength (a:ad) :=
  match a with
  | ad_z => infty
  | ad_x p => ni (ad_plength_1 p)
  end.

Lemma ad_plength_infty : forall a:ad, ad_plength a = infty -> a = ad_z.
Proof.
  simple induction a; trivial. 
  unfold ad_plength in |- *; intros; discriminate H.
Qed.

Lemma ad_plength_zeros :
 forall (a:ad) (n:nat),
   ad_plength a = ni n -> forall k:nat, k < n -> ad_bit a k = false.
Proof.
  simple induction a; trivial. 
  simple induction p. simple induction n. intros. inversion H1.
  simple induction k. simpl in H1. discriminate H1.
  intros. simpl in H1. discriminate H1.
  simple induction k. trivial.
  generalize H0. case n. intros. inversion H3.
  intros. simpl in |- *. unfold ad_bit in H. apply (H n0). simpl in H1. inversion H1. reflexivity.
  exact (lt_S_n n1 n0 H3).
  simpl in |- *. intros n H. inversion H. intros. inversion H0.
Qed.

Lemma ad_plength_one :
 forall (a:ad) (n:nat), ad_plength a = ni n -> ad_bit a n = true.
Proof.
  simple induction a. intros. inversion H.
  simple induction p. intros. simpl in H0. inversion H0. reflexivity.
  intros. simpl in H0. inversion H0. simpl in |- *. unfold ad_bit in H. apply H. reflexivity.
  intros. simpl in H. inversion H. reflexivity.
Qed.

Lemma ad_plength_first_one :
 forall (a:ad) (n:nat),
   (forall k:nat, k < n -> ad_bit a k = false) ->
   ad_bit a n = true -> ad_plength a = ni n.
Proof.
  simple induction a. intros. simpl in H0. discriminate H0.
  simple induction p. intros. generalize H0. case n. intros. reflexivity.
  intros. absurd (ad_bit (ad_x (xI p0)) 0 = false). trivial with bool.
  auto with bool arith.
  intros. generalize H0 H1. case n. intros. simpl in H3. discriminate H3.
  intros. simpl in |- *. unfold ad_plength in H.
  cut (ni (ad_plength_1 p0) = ni n0). intro. inversion H4. reflexivity.
  apply H. intros. change (ad_bit (ad_x (xO p0)) (S k) = false) in |- *. apply H2. apply lt_n_S. exact H4.
  exact H3.
  intro. case n. trivial.
  intros. simpl in H0. discriminate H0.
Qed.

Definition ni_min (d d':natinf) :=
  match d with
  | infty => d'
  | ni n => match d' with
            | infty => d
            | ni n' => ni (min n n')
            end
  end.

Lemma ni_min_idemp : forall d:natinf, ni_min d d = d.
Proof.
  simple induction d; trivial.
  unfold ni_min in |- *.
  simple induction n; trivial.
  intros.
  simpl in |- *.
  inversion H.
  rewrite H1.
  rewrite H1.
  reflexivity.
Qed.

Lemma ni_min_comm : forall d d':natinf, ni_min d d' = ni_min d' d.
Proof.
  simple induction d. simple induction d'; trivial.
  simple induction d'; trivial. elim n. simple induction n0; trivial.
  intros. elim n1; trivial. intros. unfold ni_min in H. cut (min n0 n2 = min n2 n0).
  intro. unfold ni_min in |- *. simpl in |- *. rewrite H1. reflexivity.
  cut (ni (min n0 n2) = ni (min n2 n0)). intros.
  inversion H1; trivial.
  exact (H n2).
Qed.

Lemma ni_min_assoc :
 forall d d' d'':natinf, ni_min (ni_min d d') d'' = ni_min d (ni_min d' d'').
Proof.
  simple induction d; trivial. simple induction d'; trivial. 
  simple induction d''; trivial.
  unfold ni_min in |- *. intro. cut (min (min n n0) n1 = min n (min n0 n1)).
  intro. rewrite H. reflexivity.
  generalize n0 n1. elim n; trivial. 
  simple induction n3; trivial. simple induction n5; trivial.
  intros. simpl in |- *. auto.
Qed.

Lemma ni_min_O_l : forall d:natinf, ni_min (ni 0) d = ni 0.
Proof.
  simple induction d; trivial.
Qed.

Lemma ni_min_O_r : forall d:natinf, ni_min d (ni 0) = ni 0.
Proof.
  intros. rewrite ni_min_comm. apply ni_min_O_l.
Qed.

Lemma ni_min_inf_l : forall d:natinf, ni_min infty d = d.
Proof.
  trivial.
Qed.

Lemma ni_min_inf_r : forall d:natinf, ni_min d infty = d.
Proof.
  simple induction d; trivial.
Qed.

Definition ni_le (d d':natinf) := ni_min d d' = d.

Lemma ni_le_refl : forall d:natinf, ni_le d d.
Proof.
  exact ni_min_idemp.
Qed.

Lemma ni_le_antisym : forall d d':natinf, ni_le d d' -> ni_le d' d -> d = d'.
Proof.
  unfold ni_le in |- *. intros d d'. rewrite ni_min_comm. intro H. rewrite H. trivial.
Qed.

Lemma ni_le_trans :
 forall d d' d'':natinf, ni_le d d' -> ni_le d' d'' -> ni_le d d''.
Proof.
  unfold ni_le in |- *. intros. rewrite <- H. rewrite ni_min_assoc. rewrite H0. reflexivity.
Qed.

Lemma ni_le_min_1 : forall d d':natinf, ni_le (ni_min d d') d.
Proof.
  unfold ni_le in |- *. intros. rewrite (ni_min_comm d d'). rewrite ni_min_assoc.
  rewrite ni_min_idemp. reflexivity.
Qed.

Lemma ni_le_min_2 : forall d d':natinf, ni_le (ni_min d d') d'.
Proof.
  unfold ni_le in |- *. intros. rewrite ni_min_assoc. rewrite ni_min_idemp. reflexivity.
Qed.

Lemma ni_min_case : forall d d':natinf, ni_min d d' = d \/ ni_min d d' = d'.
Proof.
  simple induction d. intro. right. exact (ni_min_inf_l d').
  simple induction d'. left. exact (ni_min_inf_r (ni n)).
  unfold ni_min in |- *. cut (forall n0:nat, min n n0 = n \/ min n n0 = n0).
  intros. case (H n0). intro. left. rewrite H0. reflexivity.
  intro. right. rewrite H0. reflexivity.
  elim n. intro. left. reflexivity.
  simple induction n1. right. reflexivity.
  intros. case (H n2). intro. left. simpl in |- *. rewrite H1. reflexivity.
  intro. right. simpl in |- *. rewrite H1. reflexivity.
Qed.

Lemma ni_le_total : forall d d':natinf, ni_le d d' \/ ni_le d' d.
Proof.
  unfold ni_le in |- *. intros. rewrite (ni_min_comm d' d). apply ni_min_case.
Qed.

Lemma ni_le_min_induc :
 forall d d' dm:natinf,
   ni_le dm d ->
   ni_le dm d' ->
   (forall d'':natinf, ni_le d'' d -> ni_le d'' d' -> ni_le d'' dm) ->
   ni_min d d' = dm.
Proof.
  intros. case (ni_min_case d d'). intro. rewrite H2.
  apply ni_le_antisym. apply H1. apply ni_le_refl.
  exact H2.
  exact H.
  intro. rewrite H2. apply ni_le_antisym. apply H1. unfold ni_le in |- *. rewrite ni_min_comm. exact H2.
  apply ni_le_refl.
  exact H0.
Qed.

Lemma le_ni_le : forall m n:nat, m <= n -> ni_le (ni m) (ni n).
Proof.
  cut (forall m n:nat, m <= n -> min m n = m).
  intros. unfold ni_le, ni_min in |- *. rewrite (H m n H0). reflexivity.
  simple induction m. trivial.
  simple induction n0. intro. inversion H0.
  intros. simpl in |- *. rewrite (H n1 (le_S_n n n1 H1)). reflexivity.
Qed.

Lemma ni_le_le : forall m n:nat, ni_le (ni m) (ni n) -> m <= n.
Proof.
  unfold ni_le in |- *. unfold ni_min in |- *. intros. inversion H. apply le_min_r.
Qed.

Lemma ad_plength_lb :
 forall (a:ad) (n:nat),
   (forall k:nat, k < n -> ad_bit a k = false) -> ni_le (ni n) (ad_plength a).
Proof.
  simple induction a. intros. exact (ni_min_inf_r (ni n)).
  intros. unfold ad_plength in |- *. apply le_ni_le. case (le_or_lt n (ad_plength_1 p)). trivial.
  intro. absurd (ad_bit (ad_x p) (ad_plength_1 p) = false).
  rewrite
   (ad_plength_one (ad_x p) (ad_plength_1 p)
      (refl_equal (ad_plength (ad_x p)))).
  discriminate.
  apply H. exact H0.
Qed.

Lemma ad_plength_ub :
 forall (a:ad) (n:nat), ad_bit a n = true -> ni_le (ad_plength a) (ni n).
Proof.
  simple induction a. intros. discriminate H.
  intros. unfold ad_plength in |- *. apply le_ni_le. case (le_or_lt (ad_plength_1 p) n). trivial.
  intro. absurd (ad_bit (ad_x p) n = true).
  rewrite
   (ad_plength_zeros (ad_x p) (ad_plength_1 p)
      (refl_equal (ad_plength (ad_x p))) n H0).
  discriminate.
  exact H.
Qed.


(** We define an ultrametric distance between addresses: 
    $d(a,a')=1/2^pd(a,a')$, 
    where $pd(a,a')$ is the number of identical bits at the beginning 
    of $a$ and $a'$ (infinity if $a=a'$).  
    Instead of working with $d$, we work with $pd$, namely
    [ad_pdist]: *)

Definition ad_pdist (a a':ad) := ad_plength (ad_xor a a').

(** d is a distance, so $d(a,a')=0$ iff $a=a'$; this means that
    $pd(a,a')=infty$ iff $a=a'$: *)

Lemma ad_pdist_eq_1 : forall a:ad, ad_pdist a a = infty.
Proof.
  intros. unfold ad_pdist in |- *. rewrite ad_xor_nilpotent. reflexivity.
Qed.

Lemma ad_pdist_eq_2 : forall a a':ad, ad_pdist a a' = infty -> a = a'.
Proof.
  intros. apply ad_xor_eq. apply ad_plength_infty. exact H.
Qed.

(** $d$ is a distance, so $d(a,a')=d(a',a)$: *)

Lemma ad_pdist_comm : forall a a':ad, ad_pdist a a' = ad_pdist a' a.
Proof.
  unfold ad_pdist in |- *. intros. rewrite ad_xor_comm. reflexivity.
Qed.

(** $d$ is an ultrametric distance, that is, not only $d(a,a')\leq
    d(a,a'')+d(a'',a')$,
  but in fact $d(a,a')\leq max(d(a,a''),d(a'',a'))$.
  This means that $min(pd(a,a''),pd(a'',a'))<=pd(a,a')$ (lemma [ad_pdist_ultra] below).
  This follows from the fact that $a ~Ra~|a| = 1/2^{\texttt{ad\_plength}}(a))$
  is an ultrametric norm, i.e. that $|a-a'| \leq max (|a-a''|, |a''-a'|)$,
  or equivalently that $|a+b|<=max(|a|,|b|)$, i.e. that
  min $(\texttt{ad\_plength}(a), \texttt{ad\_plength}(b)) \leq 
  \texttt{ad\_plength} (a~\texttt{xor}~ b)$
  (lemma [ad_plength_ultra]).
*)

Lemma ad_plength_ultra_1 :
 forall a a':ad,
   ni_le (ad_plength a) (ad_plength a') ->
   ni_le (ad_plength a) (ad_plength (ad_xor a a')).
Proof.
  simple induction a. intros. unfold ni_le in H. unfold ad_plength at 1 3 in H.
  rewrite (ni_min_inf_l (ad_plength a')) in H.
  rewrite (ad_plength_infty a' H). simpl in |- *. apply ni_le_refl.
  intros. unfold ad_plength at 1 in |- *. apply ad_plength_lb. intros.
  cut (forall a'':ad, ad_xor (ad_x p) a' = a'' -> ad_bit a'' k = false).
  intros. apply H1. reflexivity.
  intro a''. case a''. intro. reflexivity.
  intros. rewrite <- H1. rewrite (ad_xor_semantics (ad_x p) a' k). unfold adf_xor in |- *.
  rewrite
   (ad_plength_zeros (ad_x p) (ad_plength_1 p)
      (refl_equal (ad_plength (ad_x p))) k H0).
  generalize H. case a'. trivial.
  intros. cut (ad_bit (ad_x p1) k = false). intros. rewrite H3. reflexivity.
  apply ad_plength_zeros with (n := ad_plength_1 p1). reflexivity.
  apply (lt_le_trans k (ad_plength_1 p) (ad_plength_1 p1)). exact H0.
  apply ni_le_le. exact H2.
Qed.

Lemma ad_plength_ultra :
 forall a a':ad,
   ni_le (ni_min (ad_plength a) (ad_plength a')) (ad_plength (ad_xor a a')).
Proof.
  intros. case (ni_le_total (ad_plength a) (ad_plength a')). intro.
  cut (ni_min (ad_plength a) (ad_plength a') = ad_plength a).
  intro. rewrite H0. apply ad_plength_ultra_1. exact H.
  exact H.
  intro. cut (ni_min (ad_plength a) (ad_plength a') = ad_plength a').
  intro. rewrite H0. rewrite ad_xor_comm. apply ad_plength_ultra_1. exact H.
  rewrite ni_min_comm. exact H.
Qed.

Lemma ad_pdist_ultra :
 forall a a' a'':ad,
   ni_le (ni_min (ad_pdist a a'') (ad_pdist a'' a')) (ad_pdist a a').
Proof.
  intros. unfold ad_pdist in |- *. cut (ad_xor (ad_xor a a'') (ad_xor a'' a') = ad_xor a a').
  intro. rewrite <- H. apply ad_plength_ultra.
  rewrite ad_xor_assoc. rewrite <- (ad_xor_assoc a'' a'' a'). rewrite ad_xor_nilpotent.
  rewrite ad_xor_neutral_left. reflexivity.
Qed.