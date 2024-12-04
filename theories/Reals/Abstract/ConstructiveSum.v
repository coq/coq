(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Znat.
Require Import QArith Qabs.
Require Import ConstructiveReals.
Require Import ConstructiveRealsMorphisms.
Require Import ConstructiveAbs.
Require Import ConstructiveLimits.

Local Open Scope ConstructiveReals.


(**
   Definition and properties of finite sums and powers.

   WARNING: this file is experimental and likely to change in future releases.
*)

Fixpoint CRsum {R : ConstructiveReals}
         (f:nat -> CRcarrier R) (N:nat) : CRcarrier R :=
  match N with
    | O => f 0%nat
    | S i => CRsum f i + f (S i)
  end.

Lemma CRsum_eq :
  forall {R : ConstructiveReals} (An Bn:nat -> CRcarrier R) (N:nat),
    (forall i:nat, (i <= N)%nat -> An i == Bn i) ->
    CRsum An N == CRsum Bn N.
Proof.
  induction N.
  - intros. exact (H O (Nat.le_refl _)).
  - intros. simpl. apply CRplus_morph.
    + apply IHN.
      intros. apply H. apply (Nat.le_trans _ N _ H0), le_S, Nat.le_refl.
    + apply H, Nat.le_refl.
Qed.

Lemma sum_eq_R0 : forall {R : ConstructiveReals} (un : nat -> CRcarrier R) (n : nat),
    (forall k:nat, un k == 0)
    -> CRsum un n == 0.
Proof.
  induction n.
  - intros. apply H.
  - intros. simpl. rewrite IHn.
    + rewrite H. apply CRplus_0_l.
    + exact H.
Qed.

Definition INR {R : ConstructiveReals} (n : nat) : CRcarrier R
  := CR_of_Q R (Z.of_nat n # 1).

Lemma sum_const : forall {R : ConstructiveReals} (a : CRcarrier R) (n : nat),
    CRsum (fun _ => a) n == a * INR (S n).
Proof.
  induction n.
  - unfold INR. simpl. rewrite CRmult_1_r. reflexivity.
  - simpl. rewrite IHn. unfold INR.
    replace (Z.of_nat (S (S n))) with (Z.of_nat (S n) + 1)%Z.
    + rewrite <- Qinv_plus_distr, CR_of_Q_plus, CRmult_plus_distr_l.
      apply CRplus_morph.
      * reflexivity.
      * rewrite CRmult_1_r. reflexivity.
    + replace 1%Z with (Z.of_nat 1).
      * rewrite <- Nat2Z.inj_add.
        apply f_equal. rewrite Nat.add_comm. reflexivity.
      * reflexivity.
Qed.

Lemma multiTriangleIneg : forall {R : ConstructiveReals} (u : nat -> CRcarrier R) (n : nat),
    CRabs R (CRsum u n) <= CRsum (fun k => CRabs R (u k)) n.
Proof.
  induction n.
  - apply CRle_refl.
  - simpl. apply (CRle_trans _ (CRabs R (CRsum u n) + CRabs R (u (S n)))).
    + apply CRabs_triang.
    + apply CRplus_le_compat.
      * apply IHn.
      * apply CRle_refl.
Qed.

Lemma sum_assoc : forall {R : ConstructiveReals} (u : nat -> CRcarrier R) (n p : nat),
    CRsum u (S n + p)
    == CRsum u n + CRsum (fun k => u (S n + k)%nat) p.
Proof.
  induction p.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite (Radd_assoc (CRisRing R)). apply CRplus_morph.
    + rewrite Nat.add_succ_r.
      rewrite (CRsum_eq (fun k : nat => u (S (n + k))) (fun k : nat => u (S n + k)%nat)).
      * rewrite <- IHp. reflexivity.
      * intros. reflexivity.
    + reflexivity.
Qed.

Lemma sum_Rle : forall {R : ConstructiveReals} (un vn : nat -> CRcarrier R) (n : nat),
    (forall k, le k n -> un k <= vn k)
    -> CRsum un n <= CRsum vn n.
Proof.
  induction n.
  - intros. apply H. apply Nat.le_refl.
  - intros. simpl. apply CRplus_le_compat.
    + apply IHn.
      intros. apply H. apply (Nat.le_trans _ n _ H0). apply le_S, Nat.le_refl.
    + apply H. apply Nat.le_refl.
Qed.

Lemma Abs_sum_maj : forall {R : ConstructiveReals} (un vn : nat -> CRcarrier R),
    (forall n:nat, CRabs R (un n) <= (vn n))
    -> forall n p:nat, (CRabs R (CRsum un n - CRsum un p) <=
              CRsum vn (Init.Nat.max n p) - CRsum vn (Init.Nat.min n p)).
Proof.
  intros. destruct (le_lt_dec n p).
  - destruct (Nat.le_exists_sub n p) as [k [maj _]].
    + assumption.
    + subst p. rewrite max_r. 2:assumption.
      rewrite min_l. 2:assumption.
      setoid_replace (CRsum un n - CRsum un (k + n))
        with (-(CRsum un (k + n) - CRsum un n)).
      * rewrite CRabs_opp.
        destruct k.
        -- simpl. unfold CRminus. rewrite CRplus_opp_r.
           rewrite CRplus_opp_r.
           rewrite CRabs_right; apply CRle_refl.
        -- replace (S k + n)%nat with (S n + k)%nat.
           ++ unfold CRminus. rewrite sum_assoc. rewrite sum_assoc.
              rewrite CRplus_comm.
              rewrite <- CRplus_assoc. rewrite CRplus_opp_l.
              rewrite CRplus_0_l. rewrite CRplus_comm.
              rewrite <- CRplus_assoc. rewrite CRplus_opp_l.
              rewrite CRplus_0_l.
              apply (CRle_trans _ (CRsum (fun k0 : nat => CRabs R (un (S n + k0)%nat)) k)).
              ** apply multiTriangleIneg.
              ** apply sum_Rle. intros.
                 apply H.

           ++ rewrite Nat.add_comm, Nat.add_succ_r. reflexivity.
      * unfold CRminus. rewrite CRopp_plus_distr, CRopp_involutive, CRplus_comm.
        reflexivity.
  - destruct (Nat.le_exists_sub p n) as [k [maj _]].
    + unfold lt in l.
      apply (Nat.le_trans p (S p)).
      * apply le_S. apply Nat.le_refl.
      * assumption.
    + subst n. rewrite max_l.
      * rewrite min_r.
        -- destruct k.
           ++ simpl. unfold CRminus. rewrite CRplus_opp_r.
              rewrite CRplus_opp_r. rewrite CRabs_right.
              ** apply CRle_refl.
              ** apply CRle_refl.
           ++ replace (S k + p)%nat with (S p + k)%nat.
              ** unfold CRminus.
                 rewrite sum_assoc. rewrite sum_assoc.
                 rewrite CRplus_comm.
                 rewrite <- CRplus_assoc. rewrite CRplus_opp_l.
                 rewrite CRplus_0_l. rewrite CRplus_comm.
                 rewrite <- CRplus_assoc. rewrite CRplus_opp_l.
                 rewrite CRplus_0_l.
                 apply (CRle_trans _ (CRsum (fun k0 : nat => CRabs R (un (S p + k0)%nat)) k)).
                 { apply multiTriangleIneg. }
                 apply sum_Rle. intros.
                 apply H.
              ** rewrite Nat.add_comm, Nat.add_succ_r. reflexivity.
        -- apply (Nat.le_trans p (S p)).
           ++ apply le_S. apply Nat.le_refl.
           ++ assumption.
      * apply (Nat.le_trans p (S p)).
        -- apply le_S. apply Nat.le_refl.
        -- assumption.
Qed.

Lemma cond_pos_sum : forall {R : ConstructiveReals} (un : nat -> CRcarrier R) (n : nat),
    (forall k, 0 <= un k)
    -> 0 <= CRsum un n.
Proof.
  induction n.
  - intros. apply H.
  - intros. simpl. rewrite <- CRplus_0_r.
    apply CRplus_le_compat.
    + apply IHn, H.
    + apply H.
Qed.

Lemma pos_sum_more : forall {R : ConstructiveReals} (u : nat -> CRcarrier R)
                       (n p : nat),
    (forall k:nat, 0 <= u k)
    -> le n p -> CRsum u n <= CRsum u p.
Proof.
  intros. destruct (Nat.le_exists_sub n p H0). destruct H1. subst p.
  rewrite Nat.add_comm.
  destruct x.
  - rewrite Nat.add_0_r. apply CRle_refl.
  - rewrite Nat.add_succ_r.
    replace (S (n + x)) with (S n + x)%nat.
    + rewrite sum_assoc.
      rewrite <- CRplus_0_r, CRplus_assoc.
      apply CRplus_le_compat_l. rewrite CRplus_0_l.
      apply cond_pos_sum.
      intros. apply H.
    + auto.
Qed.

Lemma sum_opp : forall {R : ConstructiveReals} (un : nat -> CRcarrier R) (n : nat),
    CRsum (fun k => - un k) n == - CRsum un n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. rewrite CRopp_plus_distr. reflexivity.
Qed.

Lemma sum_scale : forall {R : ConstructiveReals} (u : nat -> CRcarrier R) (a : CRcarrier R) (n : nat),
    CRsum (fun k : nat => u k * a) n == CRsum u n * a.
Proof.
  induction n.
  - simpl. rewrite (Rmul_comm (CRisRing R)). reflexivity.
  - simpl. rewrite IHn. rewrite CRmult_plus_distr_r.
    apply CRplus_morph.
    + reflexivity.
    + rewrite (Rmul_comm (CRisRing R)). reflexivity.
Qed.

Lemma sum_plus : forall {R : ConstructiveReals} (u v : nat -> CRcarrier R) (n : nat),
    CRsum (fun n0 : nat => u n0 + v n0) n == CRsum u n + CRsum v n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. do 2 rewrite CRplus_assoc.
    apply CRplus_morph.
    + reflexivity.
    + rewrite CRplus_comm, CRplus_assoc.
      apply CRplus_morph.
      * reflexivity.
      * apply CRplus_comm.
Qed.

Lemma decomp_sum :
  forall {R : ConstructiveReals} (An:nat -> CRcarrier R) (N:nat),
    (0 < N)%nat ->
    CRsum An N == An 0%nat + CRsum (fun i:nat => An (S i)) (pred N).
Proof.
  induction N.
  - intros. exfalso. inversion H.
  - intros _. destruct N.
    + simpl. reflexivity.
    + simpl.
      rewrite IHN.
      * rewrite CRplus_assoc.
        apply CRplus_morph.
        -- reflexivity.
        -- reflexivity.
      * apply le_n_S, Nat.le_0_l.
Qed.

Lemma reverse_sum : forall {R : ConstructiveReals} (u : nat -> CRcarrier R) (n : nat),
    CRsum u n == CRsum (fun k => u (n-k)%nat) n.
Proof.
  induction n.
  - intros. reflexivity.
  - rewrite (decomp_sum (fun k : nat => u (S n - k)%nat)).
    + simpl.
      rewrite CRplus_comm. apply CRplus_morph.
      * reflexivity.
      * assumption.
    + unfold lt. apply -> Nat.succ_le_mono; apply Nat.le_0_l.
Qed.

Lemma Rplus_le_pos : forall {R : ConstructiveReals} (a b : CRcarrier R),
    0 <= b -> a <= a + b.
Proof.
  intros. rewrite <- (CRplus_0_r a). rewrite CRplus_assoc.
  apply CRplus_le_compat_l. rewrite CRplus_0_l. assumption.
Qed.

Lemma selectOneInSum : forall {R : ConstructiveReals} (u : nat -> CRcarrier R) (n i : nat),
    le i n
    -> (forall k:nat, 0 <= u k)
    -> u i <= CRsum u n.
Proof.
  induction n.
  - intros. inversion H. subst i. apply CRle_refl.
  - intros. apply Nat.le_succ_r in H. destruct H.
    + apply (CRle_trans _ (CRsum u n)).
      * apply IHn.
        -- assumption.
        -- assumption.
      * simpl. apply Rplus_le_pos. apply H0.
    + subst i. simpl. rewrite CRplus_comm. apply Rplus_le_pos.
      apply cond_pos_sum. intros. apply H0.
Qed.

Lemma splitSum : forall {R : ConstructiveReals} (un : nat -> CRcarrier R)
                        (filter : nat -> bool) (n : nat),
    CRsum un n
    == CRsum (fun i => if filter i then un i else 0) n
       + CRsum (fun i => if filter i then 0 else un i) n.
Proof.
  induction n.
  - simpl. destruct (filter O).
    + symmetry; apply CRplus_0_r.
    + symmetry. apply CRplus_0_l.
  - simpl. rewrite IHn. clear IHn. destruct (filter (S n)).
    + do 2 rewrite CRplus_assoc. apply CRplus_morph.
      * reflexivity.
      * rewrite CRplus_comm. apply CRplus_morph.
        -- reflexivity.
        -- rewrite CRplus_0_r.
           reflexivity.
    + rewrite CRplus_0_r. rewrite CRplus_assoc. reflexivity.
Qed.

Definition series_cv {R : ConstructiveReals}
           (un : nat -> CRcarrier R) (s : CRcarrier R) : Set
  := CR_cv R (CRsum un) s.

Definition series_cv_lim_lt {R : ConstructiveReals}
           (un : nat -> CRcarrier R) (x : CRcarrier R) : Set
  := { l : CRcarrier R & prod (series_cv un l) (l < x) }.

Definition series_cv_le_lim {R : ConstructiveReals}
           (x : CRcarrier R) (un : nat -> CRcarrier R) : Set
  := { l : CRcarrier R & prod (series_cv un l) (x <= l) }.

Lemma series_cv_maj : forall {R : ConstructiveReals}
                        (un vn : nat -> CRcarrier R) (s : CRcarrier R),
    (forall n:nat, CRabs R (un n) <= vn n)
    -> series_cv vn s
    -> { l : CRcarrier R & prod (series_cv un l) (l <= s) }.
Proof.
  intros. destruct (CR_complete R (CRsum un)).
  - intros n.
    specialize (H0 (2*n)%positive) as [N maj].
    exists N. intros i j H0 H1.
    apply (CRle_trans _ (CRsum vn (max i j) - CRsum vn (min i j))).
    + apply Abs_sum_maj. apply H.
    + setoid_replace (CRsum vn (max i j) - CRsum vn (min i j))
        with (CRabs R (CRsum vn (max i j) - (CRsum vn (min i j)))).
      * setoid_replace (CRsum vn (Init.Nat.max i j) - CRsum vn (Init.Nat.min i j))
          with (CRsum vn (Init.Nat.max i j) - s - (CRsum vn (Init.Nat.min i j) - s)).
        -- apply (CRle_trans _ _ _ (CRabs_triang _ _)).
           setoid_replace (1#n)%Q with ((1#2*n) + (1#2*n))%Q.
           ++ rewrite CR_of_Q_plus.
              apply CRplus_le_compat.
              ** apply maj. apply (Nat.le_trans _ i). { assumption. } apply Nat.le_max_l.
              ** rewrite CRabs_opp. apply maj.
                 apply Nat.min_case.
                 { apply (Nat.le_trans _ i). - assumption. - apply Nat.le_refl. }
                 assumption.
           ++ rewrite Qinv_plus_distr. reflexivity.
        -- unfold CRminus. rewrite CRplus_assoc. apply CRplus_morph.
           ++ reflexivity.
           ++ rewrite CRopp_plus_distr, CRopp_involutive.
              rewrite CRplus_comm, CRplus_assoc, CRplus_opp_r, CRplus_0_r.
              reflexivity.
      * rewrite CRabs_right.
        -- reflexivity.
        -- rewrite <- (CRplus_opp_r (CRsum vn (Init.Nat.min i j))).
           apply CRplus_le_compat.
           ++ apply pos_sum_more.
              ** intros. apply (CRle_trans _ (CRabs R (un k))), H.
                 apply CRabs_pos.
              ** apply (Nat.le_trans _ i), Nat.le_max_l. apply Nat.le_min_l.
           ++ apply CRle_refl.
  - exists x. split.
    + assumption.
      (* x <= s *)
    + apply (CRplus_le_reg_r (-x)). rewrite CRplus_opp_r.
      apply (CR_cv_bound_down (fun n => CRsum vn n - CRsum un n) _ _ 0).
      * intros. rewrite <- (CRplus_opp_r (CRsum un n)).
        apply CRplus_le_compat.
        -- apply sum_Rle.
           intros. apply (CRle_trans _ (CRabs R (un k))).
           ++ apply CRle_abs.
           ++ apply H.
        -- apply CRle_refl.
      * apply CR_cv_plus.
        -- assumption.
        -- apply CR_cv_opp. assumption.
Qed.

Lemma series_cv_abs_lt
  : forall {R : ConstructiveReals} (un vn : nat -> CRcarrier R) (l : CRcarrier R),
    (forall n:nat, CRabs R (un n) <= vn n)
    -> series_cv_lim_lt vn l
    -> series_cv_lim_lt un l.
Proof.
  intros. destruct H0 as [x [H0 H1]].
  destruct (series_cv_maj un vn x H H0) as [x0 H2].
  exists x0. split.
  - apply H2.
  - apply (CRle_lt_trans _ x).
    + apply H2.
    + apply H1.
Qed.

Definition series_cv_abs {R : ConstructiveReals} (u : nat -> CRcarrier R)
  : CR_cauchy R (CRsum (fun n => CRabs R (u n)))
    -> { l : CRcarrier R & series_cv u l }.
Proof.
  intros. apply CR_complete in H. destruct H.
  destruct (series_cv_maj u (fun k => CRabs R (u k)) x).
  - intro n. apply CRle_refl.
  - assumption.
  - exists x0. apply p.
Qed.

Lemma series_cv_unique :
  forall {R : ConstructiveReals} (Un:nat -> CRcarrier R) (l1 l2:CRcarrier R),
    series_cv Un l1 -> series_cv Un l2 -> l1 == l2.
Proof.
  intros. apply (CR_cv_unique (CRsum Un)); assumption.
Qed.

Lemma series_cv_abs_eq
  : forall {R : ConstructiveReals} (u : nat -> CRcarrier R) (a : CRcarrier R)
           (cau : CR_cauchy R (CRsum (fun n => CRabs R (u n)))),
    series_cv u a
    -> (a == (let (l,_):= series_cv_abs u cau in l))%ConstructiveReals.
Proof.
  intros. destruct (series_cv_abs u cau).
  apply (series_cv_unique u).
  - exact H.
  - exact s.
Qed.

Lemma series_cv_abs_cv
  : forall {R : ConstructiveReals} (u : nat -> CRcarrier R)
           (cau : CR_cauchy R (CRsum (fun n => CRabs R (u n)))),
    series_cv u (let (l,_):= series_cv_abs u cau in l).
Proof.
  intros. destruct (series_cv_abs u cau). exact s.
Qed.

Lemma series_cv_opp : forall {R : ConstructiveReals}
                        (s : CRcarrier R) (u : nat -> CRcarrier R),
    series_cv u s
    -> series_cv (fun n => - u n) (- s).
Proof.
  intros. intros p. specialize (H p) as [N H].
  exists N. intros n H0.
  setoid_replace (CRsum (fun n0 : nat => - u n0) n - - s)
    with (-(CRsum (fun n0 : nat => u n0) n - s)).
  - rewrite CRabs_opp.
    apply H, H0.
  - unfold CRminus.
    rewrite sum_opp. rewrite CRopp_plus_distr. reflexivity.
Qed.

Lemma series_cv_scale : forall {R : ConstructiveReals}
                          (a : CRcarrier R) (s : CRcarrier R) (u : nat -> CRcarrier R),
    series_cv u s
    -> series_cv (fun n => (u n) * a) (s * a).
Proof.
  intros.
  apply (CR_cv_eq _ (fun n => CRsum u n * a)).
  - intro n. rewrite sum_scale. reflexivity.
  - apply CR_cv_scale, H.
Qed.

Lemma series_cv_plus : forall {R : ConstructiveReals}
                         (u v : nat -> CRcarrier R) (s t : CRcarrier R),
    series_cv u s
    -> series_cv v t
    -> series_cv (fun n => u n + v n) (s + t).
Proof.
  intros. apply (CR_cv_eq _ (fun n => CRsum u n + CRsum v n)).
  - intro n. symmetry. apply sum_plus.
  - apply CR_cv_plus.
    + exact H.
    + exact H0.
Qed.

Lemma series_cv_minus : forall {R : ConstructiveReals}
                          (u v : nat -> CRcarrier R) (s t : CRcarrier R),
    series_cv u s
    -> series_cv v t
    -> series_cv (fun n => u n - v n) (s - t).
Proof.
  intros. apply (CR_cv_eq _ (fun n => CRsum u n - CRsum v n)).
  - intro n. symmetry. unfold CRminus. rewrite sum_plus.
    rewrite sum_opp. reflexivity.
  - apply CR_cv_plus.
    + exact H.
    + apply CR_cv_opp. exact H0.
Qed.

Lemma series_cv_nonneg : forall {R : ConstructiveReals}
                           (u : nat -> CRcarrier R) (s : CRcarrier R),
    (forall n:nat, 0 <= u n) -> series_cv u s -> 0 <= s.
Proof.
  intros. apply (CRle_trans 0 (CRsum u 0)).
  - apply H.
  - apply (growing_ineq (CRsum u)).
    + intro n. simpl.
      rewrite <- CRplus_0_r. apply CRplus_le_compat.
      * rewrite CRplus_0_r. apply CRle_refl.
      * apply H.
    + apply H0.
Qed.

Lemma series_cv_eq : forall {R : ConstructiveReals}
                       (u v : nat -> CRcarrier R) (s : CRcarrier R),
    (forall n:nat, u n == v n)
    -> series_cv u s
    -> series_cv v s.
Proof.
  intros. intros p. specialize (H0 p). destruct H0 as [N H0].
  exists N. intros. unfold CRminus.
  rewrite <- (CRsum_eq u).
  - apply H0, H1.
  - intros. apply H.
Qed.

Lemma series_cv_remainder_maj : forall {R : ConstructiveReals} (u : nat -> CRcarrier R)
                                  (s eps : CRcarrier R)
                                  (N : nat),
    series_cv u s
    -> 0 < eps
    -> (forall n:nat, 0 <= u n)
    -> CRabs R (CRsum u N - s) <= eps
    -> forall n:nat, CRsum (fun k=> u (N + S k)%nat) n <= eps.
Proof.
  intros. pose proof (sum_assoc u N n).
  rewrite <- (CRsum_eq (fun k : nat => u (S N + k)%nat)).
  - apply (CRplus_le_reg_l (CRsum u N)). rewrite <- H3.
    apply (CRle_trans _ s).
    + apply growing_ineq.
      2: apply H.
      intro k. simpl. rewrite <- CRplus_0_r, CRplus_assoc.
      apply CRplus_le_compat_l. rewrite CRplus_0_l. apply H1.
    + rewrite CRabs_minus_sym in H2.
      rewrite CRplus_comm. apply (CRplus_le_reg_r (-CRsum u N)).
      rewrite CRplus_assoc. rewrite CRplus_opp_r. rewrite CRplus_0_r.
      apply (CRle_trans _ (CRabs R (s - CRsum u N))).
      * apply CRle_abs.
      * assumption.
  - intros. rewrite Nat.add_succ_r. reflexivity.
Qed.


Lemma series_cv_abs_remainder : forall {R : ConstructiveReals} (u : nat -> CRcarrier R)
                                  (s sAbs : CRcarrier R)
                                  (n : nat),
    series_cv u s
    -> series_cv (fun n => CRabs R (u n)) sAbs
    -> CRabs R (CRsum u n - s)
      <= sAbs - CRsum (fun n => CRabs R (u n)) n.
Proof.
  intros.
  apply (CR_cv_le (fun N => CRabs R (CRsum u n - (CRsum u (n + N))))
                   (fun N => CRsum (fun n : nat => CRabs R (u n)) (n + N)
                          - CRsum (fun n : nat => CRabs R (u n)) n)).
  - intro N. destruct N.
    + rewrite Nat.add_0_r. unfold CRminus.
      rewrite CRplus_opp_r. rewrite CRplus_opp_r.
      rewrite CRabs_right.
      * apply CRle_refl.
      * apply CRle_refl.
    + rewrite Nat.add_succ_r.
      replace (S (n + N)) with (S n + N)%nat. 2: reflexivity.
      unfold CRminus. rewrite sum_assoc. rewrite sum_assoc.
      rewrite CRopp_plus_distr.
      rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l, CRabs_opp.
      rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l.
      rewrite CRplus_0_l. apply multiTriangleIneg.
  - apply CR_cv_dist_cont. intros eps.
    specialize (H eps) as [N lim].
    exists N. intros. rewrite Nat.add_comm. apply lim. apply (Nat.le_trans N i).
    + assumption.
    + rewrite <- (Nat.add_0_r i), <- Nat.add_assoc.
      apply Nat.add_le_mono_l, Nat.le_0_l.
  - apply CR_cv_plus. 2: apply CR_cv_const. intros eps.
    specialize (H0 eps) as [N lim].
    exists N. intros. rewrite Nat.add_comm. apply lim. apply (Nat.le_trans N i).
    + assumption.
    + rewrite <- (Nat.add_0_r i), <- Nat.add_assoc.
      apply Nat.add_le_mono_l, Nat.le_0_l.
Qed.

Lemma series_cv_triangle : forall {R : ConstructiveReals}
                             (u : nat -> CRcarrier R) (s sAbs : CRcarrier R),
    series_cv u s
    -> series_cv (fun n => CRabs R (u n)) sAbs
    -> CRabs R s <= sAbs.
Proof.
  intros.
  apply (CR_cv_le (fun n => CRabs R (CRsum u n))
                   (CRsum (fun n => CRabs R (u n)))).
  - intros. apply multiTriangleIneg.
  - apply CR_cv_abs_cont. assumption.
  - assumption.
Qed.

Lemma series_cv_shift :
  forall {R : ConstructiveReals} (f : nat -> CRcarrier R) k l,
    series_cv (fun n => f (S k + n)%nat) l
    -> series_cv f (l + CRsum f k).
Proof.
  intros. intro p. specialize (H p) as [n nmaj].
  exists (S k+n)%nat. intros. destruct (Nat.le_exists_sub (S k) i).
  - apply (Nat.le_trans _ (S k + 0)).
    + rewrite Nat.add_0_r. apply Nat.le_refl.
    + apply (Nat.le_trans _ (S k + n)).
      * apply Nat.add_le_mono_l, Nat.le_0_l.
      * exact H.
  - destruct H0. subst i.
    rewrite Nat.add_comm in H. rewrite <- Nat.add_le_mono_r in H.
    specialize (nmaj x H). unfold CRminus.
    rewrite Nat.add_comm, (sum_assoc f k x).
    setoid_replace (CRsum f k + CRsum (fun k0 : nat => f (S k + k0)%nat) x - (l + CRsum f k))
      with (CRsum (fun k0 : nat => f (S k + k0)%nat) x - l).
    + exact nmaj.
    + unfold CRminus. rewrite (CRplus_comm (CRsum f k)).
      rewrite CRplus_assoc. apply CRplus_morph.
      * reflexivity.
      * rewrite CRplus_comm, CRopp_plus_distr, CRplus_assoc.
        rewrite CRplus_opp_l, CRplus_0_r. reflexivity.
Qed.

Lemma series_cv_shift' : forall {R : ConstructiveReals}
                           (un : nat -> CRcarrier R) (s : CRcarrier R) (shift : nat),
    series_cv un s
    -> series_cv (fun n => un (n+shift)%nat)
                       (s - match shift with
                            | O => 0
                            | S p => CRsum un p
                            end).
Proof.
  intros. destruct shift as [|p].
  - unfold CRminus. rewrite CRopp_0. rewrite CRplus_0_r.
    apply (series_cv_eq un).
    + intros.
      rewrite Nat.add_0_r. reflexivity.
    + apply H.
  - apply (CR_cv_eq _ (fun n => CRsum un (n + S p) - CRsum un p)).
    + intros. rewrite Nat.add_comm. unfold CRminus.
      rewrite sum_assoc. simpl. rewrite CRplus_comm, <- CRplus_assoc.
      rewrite CRplus_opp_l, CRplus_0_l.
      apply CRsum_eq. intros. rewrite (Nat.add_comm i). reflexivity.
    + apply CR_cv_plus.
      * apply (CR_cv_shift' _ (S p) _ H).
      * intros n. exists (Pos.to_nat n). intros.
        unfold CRminus. simpl.
        rewrite CRopp_involutive, CRplus_opp_l. rewrite CRabs_right.
        -- apply CR_of_Q_le. discriminate.
        -- apply CRle_refl.
Qed.

Lemma CRmorph_sum : forall {R1 R2 : ConstructiveReals}
                      (f : @ConstructiveRealsMorphism R1 R2)
                      (un : nat -> CRcarrier R1) (n : nat),
  CRmorph f (CRsum un n) ==
  CRsum (fun n0 : nat => CRmorph f (un n0)) n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite CRmorph_plus, IHn. reflexivity.
Qed.

Lemma CRmorph_INR : forall {R1 R2 : ConstructiveReals}
                      (f : @ConstructiveRealsMorphism R1 R2)
                      (n : nat),
  CRmorph f (INR n) == INR n.
Proof.
  induction n.
  - apply CRmorph_rat.
  - simpl. unfold INR.
    rewrite (CRmorph_proper f _ (1 + CR_of_Q R1 (Z.of_nat n # 1))).
    + rewrite CRmorph_plus. unfold INR in IHn.
      rewrite IHn. rewrite CRmorph_one, <- CR_of_Q_plus.
      apply CR_of_Q_morph. rewrite Qinv_plus_distr.
      unfold Qeq, Qnum, Qden. do 2 rewrite Z.mul_1_r.
      rewrite Nat2Z.inj_succ. rewrite <- Z.add_1_l. reflexivity.
    + rewrite <- CR_of_Q_plus.
      apply CR_of_Q_morph. rewrite Qinv_plus_distr.
      unfold Qeq, Qnum, Qden. do 2 rewrite Z.mul_1_r.
      rewrite Nat2Z.inj_succ. rewrite <- Z.add_1_l. reflexivity.
Qed.

Lemma CRmorph_series_cv : forall {R1 R2 : ConstructiveReals}
                     (f : @ConstructiveRealsMorphism R1 R2)
                     (un : nat -> CRcarrier R1)
                     (l : CRcarrier R1),
    series_cv un l
    -> series_cv (fun n => CRmorph f (un n)) (CRmorph f l).
Proof.
  intros.
  apply (CR_cv_eq _ (fun n => CRmorph f (CRsum un n))).
  - intro n. apply CRmorph_sum.
  - apply CRmorph_cv, H.
Qed.
