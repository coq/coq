(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i 	     $Id$	      i*)

Require Bool.
Require ZArith.
Require Arith.
Require Min.
Require Addr.

Fixpoint ad_plength_1 [p:positive] : nat :=
  Cases p of
      xH => O
    | (xI _) => O
    | (xO p') => (S (ad_plength_1 p'))
  end.

Inductive natinf : Set :=
    infty : natinf
  | ni : nat -> natinf.

Definition ad_plength := [a:ad]
  Cases a of
      ad_z => infty
    | (ad_x p) => (ni (ad_plength_1 p))
  end.

Lemma ad_plength_infty : (a:ad) (ad_plength a)=infty -> a=ad_z.
Proof.
  Induction a; Trivial. 
  Unfold ad_plength; Intros; Discriminate H.
Qed.

Lemma ad_plength_zeros : (a:ad) (n:nat) (ad_plength a)=(ni n) ->
    (k:nat) (lt k n) -> (ad_bit a k)=false.
Proof.
  Induction a; Trivial. 
  Induction p. Induction n. Intros. Inversion H1.
  Induction k. Simpl in H1. Discriminate H1.
  Intros. Simpl in H1. Discriminate H1.
  Induction k. Trivial.
  Generalize H0. Case n. Intros. Inversion H3.
  Intros. Simpl. Unfold ad_bit in H. Apply (H n0). Simpl in H1. Inversion H1. Reflexivity.
  Exact (lt_S_n n1 n0 H3).
  Simpl. Intros n H. Inversion H. Intros. Inversion H0.
Qed.

Lemma ad_plength_one : (a:ad) (n:nat) (ad_plength a)=(ni n) -> (ad_bit a n)=true.
Proof.
  Induction a. Intros. Inversion H.
  Induction p. Intros. Simpl in H0. Inversion H0. Reflexivity.
  Intros. Simpl in H0. Inversion H0. Simpl. Unfold ad_bit in H. Apply H. Reflexivity.
  Intros. Simpl in H. Inversion H. Reflexivity.
Qed.

Lemma ad_plength_first_one : (a:ad) (n:nat)
    ((k:nat) (lt k n) -> (ad_bit a k)=false) -> (ad_bit a n)=true ->
      (ad_plength a)=(ni n).
Proof.
  Induction a. Intros. Simpl in H0. Discriminate H0.
  Induction p. Intros. Generalize H0. Case n. Intros. Reflexivity.
  Intros. Absurd (ad_bit (ad_x (xI p0)) O)=false. Trivial with bool.
  Auto with bool arith.
  Intros. Generalize H0 H1. Case n. Intros. Simpl in H3. Discriminate H3.
  Intros. Simpl. Unfold ad_plength in H.
  Cut (ni (ad_plength_1 p0))=(ni n0). Intro. Inversion H4. Reflexivity.
  Apply H. Intros. Change (ad_bit (ad_x (xO p0)) (S k))=false. Apply H2. Apply lt_n_S. Exact H4.
  Exact H3.
  Intro. Case n. Trivial.
  Intros. Simpl in H0. Discriminate H0.
Qed.

Definition ni_min := [d,d':natinf]
  Cases d of
      infty => d'
    | (ni n) => Cases d' of
                    infty => d
		  | (ni n') => (ni (min n n'))
		end
  end.

Lemma ni_min_idemp : (d:natinf) (ni_min d d)=d.
Proof.
  Induction d; Trivial.
  Unfold ni_min.
  Induction n; Trivial.
  Intros.
  Simpl.
  Inversion H.
  Rewrite H1.
  Rewrite H1.
  Reflexivity.
Qed.

Lemma ni_min_comm : (d,d':natinf) (ni_min d d')=(ni_min d' d).
Proof.
  Induction d. Induction d'; Trivial.
  Induction d'; Trivial. Elim n. Induction n0; Trivial.
  Intros. Elim n1; Trivial. Intros. Unfold ni_min in H. Cut (min n0 n2)=(min n2 n0).
  Intro. Unfold ni_min. Simpl. Rewrite H1. Reflexivity.
  Cut (ni (min n0 n2))=(ni (min n2 n0)). Intros.
  Inversion H1; Trivial.
  Exact (H n2).
Qed.

Lemma ni_min_assoc : (d,d',d'':natinf) (ni_min (ni_min d d') d'')=(ni_min d (ni_min d' d'')).
Proof.
  Induction d; Trivial. Induction d'; Trivial. 
  Induction d''; Trivial.
  Unfold ni_min. Intro. Cut (min (min n n0) n1)=(min n (min n0 n1)).
  Intro. Rewrite H. Reflexivity.
  Generalize n0 n1. Elim n; Trivial. 
  Induction n3; Trivial. Induction n5; Trivial.
  Intros. Simpl. Auto.
Qed.

Lemma ni_min_O_l : (d:natinf) (ni_min (ni O) d)=(ni O).
Proof.
  Induction d; Trivial.
Qed.

Lemma ni_min_O_r : (d:natinf) (ni_min d (ni O))=(ni O).
Proof.
  Intros. Rewrite ni_min_comm. Apply ni_min_O_l.
Qed.

Lemma ni_min_inf_l : (d:natinf) (ni_min infty d)=d.
Proof.
  Trivial.
Qed.

Lemma ni_min_inf_r : (d:natinf) (ni_min d infty)=d.
Proof.
  Induction d; Trivial.
Qed.

Definition ni_le := [d,d':natinf] (ni_min d d')=d.

Lemma ni_le_refl : (d:natinf) (ni_le d d).
Proof.
  Exact ni_min_idemp.
Qed.

Lemma ni_le_antisym : (d,d':natinf) (ni_le d d') -> (ni_le d' d) -> d=d'.
Proof.
  Unfold ni_le. Intros d d'. Rewrite ni_min_comm. Intro H. Rewrite H. Trivial.
Qed.

Lemma ni_le_trans : (d,d',d'':natinf) (ni_le d d') -> (ni_le d' d'') -> (ni_le d d'').
Proof.
  Unfold ni_le. Intros. Rewrite <- H. Rewrite ni_min_assoc. Rewrite H0. Reflexivity.
Qed.

Lemma ni_le_min_1 : (d,d':natinf) (ni_le (ni_min d d') d).
Proof.
  Unfold ni_le. Intros. Rewrite (ni_min_comm d d'). Rewrite ni_min_assoc.
  Rewrite ni_min_idemp. Reflexivity.
Qed.

Lemma ni_le_min_2 : (d,d':natinf) (ni_le (ni_min d d') d').
Proof.
  Unfold ni_le. Intros. Rewrite ni_min_assoc. Rewrite ni_min_idemp. Reflexivity.
Qed.

Lemma ni_min_case : (d,d':natinf) (ni_min d d')=d \/ (ni_min d d')=d'.
Proof.
  Induction d. Intro. Right . Exact (ni_min_inf_l d').
  Induction d'. Left . Exact (ni_min_inf_r (ni n)).
  Unfold ni_min. Cut (n0:nat)(min n n0)=n\/(min n n0)=n0.
  Intros. Case (H n0). Intro. Left . Rewrite H0. Reflexivity.
  Intro. Right . Rewrite H0. Reflexivity.
  Elim n. Intro. Left . Reflexivity.
  Induction n1. Right . Reflexivity.
  Intros. Case (H n2). Intro. Left . Simpl. Rewrite H1. Reflexivity.
  Intro. Right . Simpl. Rewrite H1. Reflexivity.
Qed.

Lemma ni_le_total : (d,d':natinf) (ni_le d d') \/ (ni_le d' d).
Proof.
  Unfold ni_le. Intros. Rewrite (ni_min_comm d' d). Apply ni_min_case.
Qed.

Lemma ni_le_min_induc : (d,d',dm:natinf) (ni_le dm d) -> (ni_le dm d') ->
    ((d'':natinf) (ni_le d'' d) -> (ni_le d'' d') -> (ni_le d'' dm)) ->
      (ni_min d d')=dm.
Proof.
  Intros. Case (ni_min_case d d'). Intro. Rewrite H2.
  Apply ni_le_antisym. Apply H1. Apply ni_le_refl.
  Exact H2.
  Exact H.
  Intro. Rewrite H2. Apply ni_le_antisym. Apply H1. Unfold ni_le. Rewrite ni_min_comm. Exact H2.
  Apply ni_le_refl.
  Exact H0.
Qed.

Lemma le_ni_le : (m,n:nat) (le m n) -> (ni_le (ni m) (ni n)).
Proof.
  Cut (m,n:nat)(le m n)->(min m n)=m.
  Intros. Unfold ni_le ni_min. Rewrite (H m n H0). Reflexivity.
  Induction m. Trivial.
  Induction n0. Intro. Inversion H0.
  Intros. Simpl. Rewrite (H n1 (le_S_n n n1 H1)). Reflexivity.
Qed.

Lemma ni_le_le : (m,n:nat) (ni_le (ni m) (ni n)) -> (le m n).
Proof.
  Unfold ni_le. Unfold ni_min. Intros. Inversion H. Apply le_min_r.
Qed.

Lemma ad_plength_lb : (a:ad) (n:nat) ((k:nat) (lt k n) -> (ad_bit a k)=false) ->
    (ni_le (ni n) (ad_plength a)).
Proof.
  Induction a. Intros. Exact (ni_min_inf_r (ni n)).
  Intros. Unfold ad_plength. Apply le_ni_le. Case (le_or_lt n (ad_plength_1 p)). Trivial.
  Intro. Absurd (ad_bit (ad_x p) (ad_plength_1 p))=false.
  Rewrite (ad_plength_one (ad_x p) (ad_plength_1 p)
          (refl_equal natinf (ad_plength (ad_x p)))).
  Discriminate.
  Apply H. Exact H0.
Qed.

Lemma ad_plength_ub : (a:ad) (n:nat) (ad_bit a n)=true ->
    (ni_le (ad_plength a) (ni n)).
Proof.
  Induction a. Intros. Discriminate H.
  Intros. Unfold ad_plength. Apply le_ni_le. Case (le_or_lt (ad_plength_1 p) n). Trivial.
  Intro. Absurd (ad_bit (ad_x p) n)=true.
  Rewrite (ad_plength_zeros (ad_x p) (ad_plength_1 p)
          (refl_equal natinf (ad_plength (ad_x p))) n H0).
  Discriminate.
  Exact H.
Qed.


(** We define an ultrametric distance between addresses: 
    $d(a,a')=1/2^pd(a,a')$, 
    where $pd(a,a')$ is the number of identical bits at the beginning 
    of $a$ and $a'$ (infinity if $a=a'$).  
    Instead of working with $d$, we work with $pd$, namely
    [ad_pdist]: *)

Definition ad_pdist := [a,a':ad] (ad_plength (ad_xor a a')).

(** d is a distance, so $d(a,a')=0$ iff $a=a'$; this means that
    $pd(a,a')=infty$ iff $a=a'$: *)

Lemma ad_pdist_eq_1 : (a:ad) (ad_pdist a a)=infty.
Proof.
  Intros. Unfold ad_pdist. Rewrite ad_xor_nilpotent. Reflexivity.
Qed.

Lemma ad_pdist_eq_2 : (a,a':ad) (ad_pdist a a')=infty -> a=a'.
Proof.
  Intros. Apply ad_xor_eq. Apply ad_plength_infty. Exact H.
Qed.

(** $d$ is a distance, so $d(a,a')=d(a',a)$: *)

Lemma ad_pdist_comm : (a,a':ad) (ad_pdist a a')=(ad_pdist a' a).
Proof.
  Unfold ad_pdist. Intros. Rewrite ad_xor_comm. Reflexivity.
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

Lemma ad_plength_ultra_1 : (a,a':ad)
    (ni_le (ad_plength a) (ad_plength a')) ->
      (ni_le (ad_plength a) (ad_plength (ad_xor a a'))).
Proof.
  Induction a. Intros. Unfold ni_le in H. Unfold 1 3 ad_plength in H.
  Rewrite (ni_min_inf_l (ad_plength a')) in H.
  Rewrite (ad_plength_infty a' H). Simpl. Apply ni_le_refl.
  Intros. Unfold 1 ad_plength. Apply ad_plength_lb. Intros.
  Cut (a'':ad)(ad_xor (ad_x p) a')=a''->(ad_bit a'' k)=false.
  Intros. Apply H1. Reflexivity.
  Intro a''. Case a''. Intro. Reflexivity.
  Intros. Rewrite <- H1. Rewrite (ad_xor_semantics (ad_x p) a' k). Unfold adf_xor.
  Rewrite (ad_plength_zeros (ad_x p) (ad_plength_1 p)
          (refl_equal natinf (ad_plength (ad_x p))) k H0).
  Generalize H. Case a'. Trivial.
  Intros. Cut (ad_bit (ad_x p1) k)=false. Intros. Rewrite H3. Reflexivity.
  Apply ad_plength_zeros with n:=(ad_plength_1 p1). Reflexivity.
  Apply (lt_le_trans k (ad_plength_1 p) (ad_plength_1 p1)). Exact H0.
  Apply ni_le_le. Exact H2.
Qed.

Lemma ad_plength_ultra : (a,a':ad)
    (ni_le (ni_min (ad_plength a) (ad_plength a')) (ad_plength (ad_xor a a'))).
Proof.
  Intros. Case (ni_le_total (ad_plength a) (ad_plength a')). Intro.
  Cut (ni_min (ad_plength a) (ad_plength a'))=(ad_plength a).
  Intro. Rewrite H0. Apply ad_plength_ultra_1. Exact H.
  Exact H.
  Intro. Cut (ni_min (ad_plength a) (ad_plength a'))=(ad_plength a').
  Intro. Rewrite H0. Rewrite ad_xor_comm. Apply ad_plength_ultra_1. Exact H.
  Rewrite ni_min_comm. Exact H.
Qed.

Lemma ad_pdist_ultra : (a,a',a'':ad)
    (ni_le (ni_min (ad_pdist a a'') (ad_pdist a'' a')) (ad_pdist a a')).
Proof.
  Intros. Unfold ad_pdist. Cut (ad_xor (ad_xor a a'') (ad_xor a'' a'))=(ad_xor a a').
  Intro. Rewrite <- H. Apply ad_plength_ultra.
  Rewrite ad_xor_assoc. Rewrite <- (ad_xor_assoc a'' a'' a'). Rewrite ad_xor_nilpotent.
  Rewrite ad_xor_neutral_left. Reflexivity.
Qed.
