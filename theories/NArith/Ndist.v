(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i 	     $Id$	      i*)

Require Import Arith.
Require Import Min.
Require Import BinPos.
Require Import BinNat.
Require Import Ndigits.

(** An ultrametric distance over [N] numbers *)

Inductive natinf : Set :=
  | infty : natinf
  | ni : nat -> natinf.

Fixpoint Pplength (p:positive) : nat :=
  match p with
  | xH => 0
  | xI _ => 0
  | xO p' => S (Pplength p')
  end.

Definition Nplength (a:N) :=
  match a with
  | N0 => infty
  | Npos p => ni (Pplength p)
  end.

Lemma Nplength_infty : forall a:N, Nplength a = infty -> a = N0.
Proof.
  simple induction a; trivial. 
  unfold Nplength in |- *; intros; discriminate H.
Qed.

Lemma Nplength_zeros :
 forall (a:N) (n:nat),
   Nplength a = ni n -> forall k:nat, k < n -> Nbit a k = false.
Proof.
  simple induction a; trivial. 
  simple induction p. simple induction n. intros. inversion H1.
  simple induction k. simpl in H1. discriminate H1.
  intros. simpl in H1. discriminate H1.
  simple induction k. trivial.
  generalize H0. case n. intros. inversion H3.
  intros. simpl in |- *. unfold Nbit in H. apply (H n0). simpl in H1. inversion H1. reflexivity.
  exact (lt_S_n n1 n0 H3).
  simpl in |- *. intros n H. inversion H. intros. inversion H0.
Qed.

Lemma Nplength_one :
 forall (a:N) (n:nat), Nplength a = ni n -> Nbit a n = true.
Proof.
  simple induction a. intros. inversion H.
  simple induction p. intros. simpl in H0. inversion H0. reflexivity.
  intros. simpl in H0. inversion H0. simpl in |- *. unfold Nbit in H. apply H. reflexivity.
  intros. simpl in H. inversion H. reflexivity.
Qed.

Lemma Nplength_first_one :
 forall (a:N) (n:nat),
   (forall k:nat, k < n -> Nbit a k = false) ->
   Nbit a n = true -> Nplength a = ni n.
Proof.
  simple induction a. intros. simpl in H0. discriminate H0.
  simple induction p. intros. generalize H0. case n. intros. reflexivity.
  intros. absurd (Nbit (Npos (xI p0)) 0 = false). trivial with bool.
  auto with bool arith.
  intros. generalize H0 H1. case n. intros. simpl in H3. discriminate H3.
  intros. simpl in |- *. unfold Nplength in H.
  cut (ni (Pplength p0) = ni n0). intro. inversion H4. reflexivity.
  apply H. intros. change (Nbit (Npos (xO p0)) (S k) = false) in |- *. apply H2. apply lt_n_S. exact H4.
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

Lemma Nplength_lb :
 forall (a:N) (n:nat),
   (forall k:nat, k < n -> Nbit a k = false) -> ni_le (ni n) (Nplength a).
Proof.
  simple induction a. intros. exact (ni_min_inf_r (ni n)).
  intros. unfold Nplength in |- *. apply le_ni_le. case (le_or_lt n (Pplength p)). trivial.
  intro. absurd (Nbit (Npos p) (Pplength p) = false).
  rewrite
   (Nplength_one (Npos p) (Pplength p)
      (refl_equal (Nplength (Npos p)))).
  discriminate.
  apply H. exact H0.
Qed.

Lemma Nplength_ub :
 forall (a:N) (n:nat), Nbit a n = true -> ni_le (Nplength a) (ni n).
Proof.
  simple induction a. intros. discriminate H.
  intros. unfold Nplength in |- *. apply le_ni_le. case (le_or_lt (Pplength p) n). trivial.
  intro. absurd (Nbit (Npos p) n = true).
  rewrite
   (Nplength_zeros (Npos p) (Pplength p)
      (refl_equal (Nplength (Npos p))) n H0).
  discriminate.
  exact H.
Qed.


(** We define an ultrametric distance between [N] numbers: 
    $d(a,a')=1/2^pd(a,a')$, 
    where $pd(a,a')$ is the number of identical bits at the beginning 
    of $a$ and $a'$ (infinity if $a=a'$).  
    Instead of working with $d$, we work with $pd$, namely
    [Npdist]: *)

Definition Npdist (a a':N) := Nplength (Nxor a a').

(** d is a distance, so $d(a,a')=0$ iff $a=a'$; this means that
    $pd(a,a')=infty$ iff $a=a'$: *)

Lemma Npdist_eq_1 : forall a:N, Npdist a a = infty.
Proof.
  intros. unfold Npdist in |- *. rewrite Nxor_nilpotent. reflexivity.
Qed.

Lemma Npdist_eq_2 : forall a a':N, Npdist a a' = infty -> a = a'.
Proof.
  intros. apply Nxor_eq. apply Nplength_infty. exact H.
Qed.

(** $d$ is a distance, so $d(a,a')=d(a',a)$: *)

Lemma Npdist_comm : forall a a':N, Npdist a a' = Npdist a' a.
Proof.
  unfold Npdist in |- *. intros. rewrite Nxor_comm. reflexivity.
Qed.

(** $d$ is an ultrametric distance, that is, not only $d(a,a')\leq
    d(a,a'')+d(a'',a')$,
  but in fact $d(a,a')\leq max(d(a,a''),d(a'',a'))$.
  This means that $min(pd(a,a''),pd(a'',a'))<=pd(a,a')$ (lemma [Npdist_ultra] below).
  This follows from the fact that $a ~Ra~|a| = 1/2^{\texttt{Nplength}}(a))$
  is an ultrametric norm, i.e. that $|a-a'| \leq max (|a-a''|, |a''-a'|)$,
  or equivalently that $|a+b|<=max(|a|,|b|)$, i.e. that
  min $(\texttt{Nplength}(a), \texttt{Nplength}(b)) \leq 
  \texttt{Nplength} (a~\texttt{xor}~ b)$
  (lemma [Nplength_ultra]).
*)

Lemma Nplength_ultra_1 :
 forall a a':N,
   ni_le (Nplength a) (Nplength a') ->
   ni_le (Nplength a) (Nplength (Nxor a a')).
Proof.
  simple induction a. intros. unfold ni_le in H. unfold Nplength at 1 3 in H.
  rewrite (ni_min_inf_l (Nplength a')) in H.
  rewrite (Nplength_infty a' H). simpl in |- *. apply ni_le_refl.
  intros. unfold Nplength at 1 in |- *. apply Nplength_lb. intros.
  cut (forall a'':N, Nxor (Npos p) a' = a'' -> Nbit a'' k = false).
  intros. apply H1. reflexivity.
  intro a''. case a''. intro. reflexivity.
  intros. rewrite <- H1. rewrite (Nxor_semantics (Npos p) a' k). unfold xorf in |- *.
  rewrite
   (Nplength_zeros (Npos p) (Pplength p)
      (refl_equal (Nplength (Npos p))) k H0).
  generalize H. case a'. trivial.
  intros. cut (Nbit (Npos p1) k = false). intros. rewrite H3. reflexivity.
  apply Nplength_zeros with (n := Pplength p1). reflexivity.
  apply (lt_le_trans k (Pplength p) (Pplength p1)). exact H0.
  apply ni_le_le. exact H2.
Qed.

Lemma Nplength_ultra :
 forall a a':N,
   ni_le (ni_min (Nplength a) (Nplength a')) (Nplength (Nxor a a')).
Proof.
  intros. case (ni_le_total (Nplength a) (Nplength a')). intro.
  cut (ni_min (Nplength a) (Nplength a') = Nplength a).
  intro. rewrite H0. apply Nplength_ultra_1. exact H.
  exact H.
  intro. cut (ni_min (Nplength a) (Nplength a') = Nplength a').
  intro. rewrite H0. rewrite Nxor_comm. apply Nplength_ultra_1. exact H.
  rewrite ni_min_comm. exact H.
Qed.

Lemma Npdist_ultra :
 forall a a' a'':N,
   ni_le (ni_min (Npdist a a'') (Npdist a'' a')) (Npdist a a').
Proof.
  intros. unfold Npdist in |- *. cut (Nxor (Nxor a a'') (Nxor a'' a') = Nxor a a').
  intro. rewrite <- H. apply Nplength_ultra.
  rewrite Nxor_assoc. rewrite <- (Nxor_assoc a'' a'' a'). rewrite Nxor_nilpotent.
  rewrite Nxor_neutral_left. reflexivity.
Qed.