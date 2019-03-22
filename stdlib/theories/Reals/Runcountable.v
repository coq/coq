(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Rfunctions.
Require Import Coq.Reals.RIneq.
Require Import Coq.Logic.FinFun.
Require Import Coq.Logic.ConstructiveEpsilon.


Definition enumeration (A : Type) (u : nat -> A) (v : A -> nat) : Prop :=
  (forall x : A, u (v x) = x) /\ (forall n : nat, v (u n) = n).

Definition in_holed_interval (a b hole : R) (u : nat -> R) (n : nat) : Prop :=
  Rlt a (u n) /\ Rlt (u n) b /\ u n <> hole.

(* Here we use axiom total_order_T, which is not constructive *)
Lemma in_holed_interval_dec (a b h : R) (u : nat -> R) (n : nat)
  : {in_holed_interval a b h u n} + {~in_holed_interval a b h u n}.
Proof.
  destruct (total_order_T a (u n)) as [[l|e]|hi].
  - destruct (total_order_T b (u n)) as [[lb|eb]|hb].
    + right. intro H. destruct H. destruct H0. apply Rlt_asym in H0. contradiction.
    + subst. right. intro H. destruct H. destruct H0.
      pose proof (Rlt_asym (u n) (u n) H0). contradiction.
    + destruct (Req_EM_T h (u n)). subst. right. intro H. destruct H. destruct H0.
      exact (H1 eq_refl). left. split. assumption. split. assumption. intro H. subst.
      exact (n0 eq_refl).
  - subst. right. intro H. destruct H. pose proof (Rlt_asym (u n) (u n) H). contradiction.
  - right. intro H. destruct H. apply Rlt_asym in H. contradiction.
Qed.

Definition point_in_holed_interval (a b h : R) : R :=
  if Req_EM_T h (Rdiv (Rplus a b) (INR 2)) then (Rdiv (Rplus a h) (INR 2))
  else (Rdiv (Rplus a b) (INR 2)).

Lemma middle_in_interval : forall a b : R, Rlt a b -> (a < (a + b) / INR 2 < b)%R.
Proof.
  intros.
  assert (twoNotZero: INR 2 <> 0%R).
  { apply not_0_INR. intro abs. inversion abs. }
  assert (twoAboveZero : (0 < / INR 2)%R).
  { apply Rinv_0_lt_compat. apply lt_0_INR. apply le_n_S. apply le_S. apply le_n. }
  assert (double : forall x : R, Rplus x x = ((INR 2) * x)%R).
  { intro x. rewrite -> S_O_plus_INR. rewrite -> Rmult_plus_distr_r.
    rewrite -> Rmult_1_l. reflexivity. }
  split.
  - assert (a + a < a + b)%R. { apply (Rplus_lt_compat_l a a b). assumption. }
    rewrite -> double in H0. apply (Rmult_lt_compat_l (/ (INR 2))) in H0.
    rewrite <- Rmult_assoc in H0. rewrite -> Rinv_l in H0. simpl in H0.
    rewrite -> Rmult_1_l in H0. rewrite -> Rmult_comm in H0. assumption.
    assumption. assumption.
  - assert (b + a < b + b)%R. { apply (Rplus_lt_compat_l b a b). assumption. }
    rewrite -> Rplus_comm in H0. rewrite -> double in H0.
    apply (Rmult_lt_compat_l (/ (INR 2))) in H0.
    rewrite <- Rmult_assoc in H0. rewrite -> Rinv_l in H0. simpl in H0.
    rewrite -> Rmult_1_l in H0. rewrite -> Rmult_comm in H0. assumption.
    assumption. assumption.
Qed.

Lemma point_in_holed_interval_works (a b h : R) :
  Rlt a b -> let p := point_in_holed_interval a b h in
             Rlt a p /\ Rlt p b /\ p <> h.
Proof.
  intros. unfold point_in_holed_interval in p.
  pose proof (middle_in_interval a b H). destruct H0.
  destruct (Req_EM_T h ((a + b) / INR 2)).
  - (* middle hole, p is quarter *) subst.
    pose proof (middle_in_interval a ((a + b) / INR 2) H0). destruct H2.
    split. assumption. split. apply (Rlt_trans p ((a + b) / INR 2)%R). assumption.
    assumption. apply Rlt_not_eq. assumption.
  - split. assumption. split. assumption. intro abs. subst. contradiction.
Qed.

(* An enumeration of R reaches any open interval of R,
   extract the first two real numbers in it. *)
Definition first_in_holed_interval (u : nat -> R) (v : R -> nat) (a b h : R)
  : enumeration R u v -> Rlt a b
    -> { n : nat | in_holed_interval a b h u n
                /\ forall k : nat, k < n -> ~in_holed_interval a b h u k }.
Proof.
  intros. apply epsilon_smallest. apply (in_holed_interval_dec a b h u).
  exists (v (point_in_holed_interval a b h)).
  destruct H. unfold in_holed_interval. rewrite -> H.
  apply point_in_holed_interval_works. assumption.
Defined.

Lemma first_in_holed_interval_works (u : nat -> R) (v : R -> nat) (a b h : R)
  (pen : enumeration R u v) (plow : Rlt a b) :
  let (c,_) := first_in_holed_interval u v a b h pen plow in
  forall x:R, Rlt a x -> Rlt x b -> x <> h -> x <> u c -> c < v x.
Proof.
  destruct (first_in_holed_interval u v a b h pen plow) as [c]. intros.
  destruct (c ?= v x) eqn:order.
  - exfalso. apply Nat.compare_eq_iff in order. rewrite -> order in H2.
    destruct pen. rewrite -> H3 in H2. exact (H2 eq_refl).
  - apply Nat.compare_lt_iff in order. assumption.
  - exfalso. apply Nat.compare_gt_iff in order.
    destruct a0. specialize (H4 (v x) order). assert (in_holed_interval a b h u (v x)).
    { destruct pen. split. rewrite -> H5. assumption. rewrite -> H5. split; assumption. }
    contradiction.
Qed.

Definition first_two_in_interval (u : nat -> R) (v : R -> nat) (a b : R)
           (pen : enumeration R u v) (plow : Rlt a b)
  : prod R R :=
  let (first_index, pr) := first_in_holed_interval u v a b b pen plow in
  let (second_index, pr2) := first_in_holed_interval u v a b (u first_index) pen plow in
  if Rle_dec (u first_index) (u second_index) then (u first_index, u second_index)
  else (u second_index, u first_index).


Lemma split_couple_eq : forall a b c d : R, (a,b) = (c,d) -> a = c /\ b = d.
Proof.
  intros. injection H. intros. split. subst. reflexivity. subst. reflexivity.
Qed.

Lemma first_two_in_interval_works (u : nat -> R) (v : R -> nat) (a b : R)
  (pen : enumeration R u v) (plow : Rlt a b) :
  let (c,d) := first_two_in_interval u v a b pen plow in
  Rlt a c /\ Rlt c b
  /\ Rlt a d /\ Rlt d b
  /\ Rlt c d
  /\ (forall x:R, Rlt a x -> Rlt x b -> x <> c -> x <> d -> v c < v x).
Proof.
  intros. destruct (first_two_in_interval u v a b) eqn:ft.
  unfold first_two_in_interval in ft.
  pose proof (first_in_holed_interval_works u v a b b pen plow).
  destruct (first_in_holed_interval u v a b b pen plow) as [first_index pr].
  pose proof (first_in_holed_interval_works u v a b (u first_index) pen plow).
  destruct pr. destruct H1. destruct H3.
  destruct (first_in_holed_interval u v a b (u first_index) pen plow)
    as [second_index pr2].
  destruct pr2. destruct H5. destruct H7.
  destruct (Rle_dec (u first_index) (u second_index)).
  - apply split_couple_eq in ft as [ft ft0]. subst. split. assumption.
    split. assumption. split. assumption. split. assumption. split.
    apply Rle_lt_or_eq_dec in r1. destruct r1. assumption. exfalso.
    rewrite -> e in H8. exact (H8 eq_refl). intros. destruct pen. rewrite -> H14.
    apply H. assumption. assumption. apply Rlt_not_eq. assumption. assumption.
  - apply split_couple_eq in ft as [ft ft0]. subst. split. assumption.
    split. assumption. split. assumption. split. assumption. split.
    apply Rnot_le_lt in n. assumption. intros. destruct pen. rewrite -> H14.
    apply H0. assumption. assumption. assumption. assumption.
Qed.

(* If u,v is an enumeration of R, this sequence of open intervals
   tears the segment [0,1]. The recursive definition needs the proof that the
   previous interval is ordered, hence the type.

   The first sequence is increasing, the second decreasing.
   The first is below the second.
   Therefore the first sequence has a limit, a least upper bound b, that u cannot reach,
   which contradicts u (v b) = b. *)
Definition tearing_sequences (u : nat -> R) (v : R -> nat)
  : (enumeration R u v) -> nat -> { ab : prod R R | Rlt (fst ab) (snd ab) }.
Proof.
  intro pen. apply nat_rec.
  - exists (INR 0, INR 1). simpl. apply Rlt_0_1.
  - intros n [[a b] pr]. exists (first_two_in_interval u v a b pen pr).
    pose proof (first_two_in_interval_works u v a b pen pr).
    destruct (first_two_in_interval u v a b pen pr). apply H.
Defined.

Lemma tearing_sequences_projsig (u : nat -> R) (v : R -> nat) (en : enumeration R u v)
      (n : nat)
  : let (I,pr) := tearing_sequences u v en n in
    proj1_sig (tearing_sequences u v en (S n))
    = first_two_in_interval u v (fst I) (snd I) en pr.
Proof.
  simpl. destruct (tearing_sequences u v en n) as [[a b] pr]. simpl. reflexivity.
Qed.

(* The first tearing sequence in increasing, the second decreasing.
   That means the tearing sequences are nested intervals. *)
Lemma tearing_sequences_inc_dec (u : nat -> R) (v : R -> nat) (pen : enumeration R u v)
  : forall n : nat,
    let I := proj1_sig (tearing_sequences u v pen n) in
    let SI := proj1_sig (tearing_sequences u v pen (S n)) in
    Rlt (fst I) (fst SI) /\ Rlt (snd SI) (snd I).
Proof.
  intro n. simpl. destruct (tearing_sequences u v pen n) as [[a b] pr].
  simpl. pose proof (first_two_in_interval_works u v a b pen pr).
  destruct (first_two_in_interval u v a b pen pr).
  simpl. split. destruct H. assumption.
  destruct H as [H1 [H2 [H3 [H4 H5]]]]. assumption.
Qed.

Lemma split_lt_succ : forall n m : nat, lt n (S m) -> lt n m \/ n = m.
Proof.
  intros n m. generalize dependent n. induction m.
  - intros. destruct n. right. reflexivity. exfalso. inversion H. inversion H1.
  - intros. destruct n. left. unfold lt. apply le_n_S. apply le_0_n.
    apply lt_pred in H. simpl in H. specialize (IHm n H). destruct IHm. left. apply lt_n_S. assumption.
    subst. right. reflexivity.
Qed.

Lemma increase_seq_transit (u : nat -> R) :
  (forall n : nat, Rlt (u n) (u (S n))) -> (forall n m : nat, n < m -> Rlt (u n) (u m)).
Proof.
  intros. induction m.
  - intros. inversion H0.
  - intros. destruct (split_lt_succ n m H0).
    + apply (Rlt_trans (u n) (u m)). apply IHm. assumption. apply H.
    + subst. apply H.
Qed.

Lemma decrease_seq_transit (u : nat -> R) :
  (forall n : nat, Rlt (u (S n)) (u n)) -> (forall n m : nat, n < m -> Rlt (u m) (u n)).
Proof.
  intros. induction m.
  - intros. inversion H0.
  - intros. destruct (split_lt_succ n m H0).
    + apply (Rlt_trans (u (S m)) (u m)). apply H. apply IHm. assumption.
    + subst. apply H.
Qed.

(* Either increase the first sequence, or decrease the second sequence,
   until n = m and conclude by tearing_sequences_ordered *)
Lemma tearing_sequences_ordered_forall (u : nat -> R) (v : R -> nat)
      (pen : enumeration R u v) :
  forall n m : nat, let In := proj1_sig (tearing_sequences u v pen n) in
             let Im := proj1_sig (tearing_sequences u v pen m) in
             Rlt (fst In) (snd Im).
Proof.
  intros. destruct (tearing_sequences u v pen n) eqn:tn. simpl in In.
  destruct (tearing_sequences u v pen m) eqn:tm. simpl in Im.
  destruct (n ?= m) eqn:order.
  - apply Nat.compare_eq_iff in order. subst. rewrite -> tm in tn.
    inversion tn. subst. assumption.
  - apply Nat.compare_lt_iff in order. (* increase first sequence *)
    apply (Rlt_trans (fst In) (fst Im)).
    remember (fun n => fst (proj1_sig (tearing_sequences u v pen n))) as fseq.
    pose proof (increase_seq_transit fseq).
    assert ((forall n : nat, (fseq n < fseq (S n))%R)).
    { intro n0. rewrite -> Heqfseq. pose proof (tearing_sequences_inc_dec u v pen n0).
      destruct (tearing_sequences u v pen (S n0)). simpl.
      destruct ((tearing_sequences u v pen n0)). apply H0. }
    specialize (H H0). rewrite -> Heqfseq in H. specialize (H n m order).
    rewrite -> tn in H. rewrite -> tm in H. simpl in H. apply H. assumption.
  - apply Nat.compare_gt_iff in order. (* decrease second sequence *)
    apply (Rlt_trans (fst In) (snd In)). assumption.
    remember (fun n => snd (proj1_sig (tearing_sequences u v pen n))) as sseq.
    pose proof (decrease_seq_transit sseq).
    assert ((forall n : nat, (sseq (S n) < sseq n)%R)).
    { intro n0. rewrite -> Heqsseq. pose proof (tearing_sequences_inc_dec u v pen n0).
      destruct (tearing_sequences u v pen (S n0)). simpl.
      destruct ((tearing_sequences u v pen n0)). apply H0. }
    specialize (H H0). rewrite -> Heqsseq in H. specialize (H m n order).
    rewrite -> tn in H. rewrite -> tm in H. apply H.
Qed.

Definition tearing_elem_fst (u : nat -> R) (v : R -> nat) (pen : enumeration R u v) (x : R)
  := exists n : nat, x = fst (proj1_sig (tearing_sequences u v pen n)).

(* The limit of the first tearing sequence cannot be reached by u *)
Definition torn_number (u : nat -> R) (v : R -> nat) (pen : enumeration R u v) :
  {m : R | is_lub (tearing_elem_fst u v pen) m}.
Proof.
  intros. assert (bound (tearing_elem_fst u v pen)).
  { exists (INR 1). intros x H0. destruct H0 as [n H0]. subst. left.
    apply (tearing_sequences_ordered_forall u v pen n 0). }
  apply (completeness (tearing_elem_fst u v pen) H).
  exists (INR 0). exists 0. reflexivity.
Defined.

Lemma torn_number_above_first_sequence (u : nat -> R) (v : R -> nat) (en : enumeration R u v)
  : forall n : nat, Rlt (fst (proj1_sig (tearing_sequences u v en n)))
                 (proj1_sig (torn_number u v en)).
Proof.
  intros. destruct (torn_number u v en) as [torn i]. simpl.
  destruct (Rlt_le_dec (fst (proj1_sig (tearing_sequences u v en n))) torn).
  assumption. exfalso.
  destruct i. (* Apply the first sequence once to make the inequality strict *)
  assert (Rlt torn (fst (proj1_sig (tearing_sequences u v en (S n))))).
  { apply (Rle_lt_trans torn (fst (proj1_sig (tearing_sequences u v en n)))).
    assumption. apply tearing_sequences_inc_dec. }
  clear r. specialize (H (fst (proj1_sig (tearing_sequences u v en (S n))))).
  assert (tearing_elem_fst u v en (fst (proj1_sig (tearing_sequences u v en (S n))))).
  { exists (S n). reflexivity. }
  specialize (H H2). assert (Rlt torn torn).
  { apply (Rlt_le_trans torn (fst (proj1_sig (tearing_sequences u v en (S n)))));
      assumption. }
  apply Rlt_irrefl in H3. contradiction.
Qed.

(* The torn number is between both tearing sequences, so it could have been chosen
   at each step. *)
Lemma torn_number_below_second_sequence (u : nat -> R) (v : R -> nat)
      (en : enumeration R u v) :
  forall n : nat, Rlt (proj1_sig (torn_number u v en))
               (snd (proj1_sig (tearing_sequences u v en n))).
Proof.
  intros. destruct (torn_number u v en) as [torn i]. simpl.
  destruct (Rlt_le_dec torn (snd (proj1_sig (tearing_sequences u v en n))))
    as [l|h].
  - assumption.
  - exfalso. (* Apply the second sequence once to make the inequality strict *)
    assert (Rlt (snd (proj1_sig (tearing_sequences u v en (S n)))) torn).
    { apply (Rlt_le_trans (snd (proj1_sig (tearing_sequences u v en (S n))))
                          (snd (proj1_sig (tearing_sequences u v en n))) torn).
      apply (tearing_sequences_inc_dec u v en n). assumption. }
    clear h. (* Then prove snd (tearing_sequences u v (S n)) is an upper bound of the first
                sequence. It will yield the contradiction torn < torn. *)
    assert (is_upper_bound (tearing_elem_fst u v en)
                           (snd (proj1_sig (tearing_sequences u v en (S n))))).
    { intros x H0. destruct H0. subst. left. apply tearing_sequences_ordered_forall. }
    destruct i. apply H2 in H0.
    pose proof (Rle_lt_trans torn (snd (proj1_sig (tearing_sequences u v en (S n)))) torn H0 H).
    apply Rlt_irrefl in H3. contradiction.
Qed.

(* Here is the contradiction : the torn number's index is above a sequence
   that tends to infinity *)
Lemma limit_index_above_all_indices (u : nat -> R) (v : R -> nat) (en : enumeration R u v) :
  forall n : nat, v (fst (proj1_sig (tearing_sequences u v en (S n))))
           < v (proj1_sig (torn_number u v en)).
Proof.
  intros. simpl. destruct (tearing_sequences u v en n) as [[r r0] H] eqn:tear.
  (* The torn number was not chosen, so its index is above *)
  simpl.
  pose proof (first_two_in_interval_works u v r r0 en H).
  destruct (first_two_in_interval u v r r0) eqn:ft. simpl.
  assert (proj1_sig (tearing_sequences u v en (S n)) = (r1, r2)).
  { simpl. rewrite -> tear. assumption. }
  apply H0.
  - pose proof (torn_number_above_first_sequence u v en n). rewrite -> tear in H2. assumption.
  - pose proof (torn_number_below_second_sequence u v en n). rewrite -> tear in H2. assumption.
  - pose proof (torn_number_above_first_sequence u v en (S n)). rewrite -> H1 in H2. simpl in H2.
    intro H5. subst. apply Rlt_irrefl in H2. contradiction.
  - pose proof (torn_number_below_second_sequence u v en (S n)). rewrite -> H1 in H2. simpl in H2.
    intro H5. subst. apply Rlt_irrefl in H2. contradiction.
Qed.

(* The indices increase because each time the minimum index is chosen *)
Lemma first_indices_increasing (u : nat -> R) (v : R -> nat) (H : enumeration R u v)
  : forall n : nat, n <> 0 -> v (fst (proj1_sig (tearing_sequences u v H n)))
                     < v (fst (proj1_sig (tearing_sequences u v H (S n)))).
Proof.
  intros. destruct n. contradiction.
  (* The n+1 and n+2 intervals are drawn from the n-th interval, which we note r r0 *)
  destruct (tearing_sequences u v H n) as [[r r0] H1] eqn:In. simpl in H1.
  (* Draw the n+1 interval *)
  destruct (tearing_sequences u v H (S n)) as [[r1 r2] H2] eqn:ISn. simpl in H2.
  (* Draw the n+2 interval *)
  destruct (tearing_sequences u v H (S (S n))) as [[r3 r4] H3] eqn:ISSn. simpl in H3.
  simpl.

  assert ((r1,r2) = first_two_in_interval u v r r0 H H1).
  { simpl in ISn. rewrite -> In in ISn. inversion ISn. reflexivity. }
  assert ((r3,r4) = first_two_in_interval u v r1 r2 H H2).
  { pose proof (tearing_sequences_projsig u v H (S n)). rewrite -> ISn in H5.
    rewrite -> ISSn in H5. apply H5. }

  pose proof (first_two_in_interval_works u v r r0 H H1) as firstChoiceWorks.
  rewrite <- H4 in firstChoiceWorks.
  destruct firstChoiceWorks as [fth [fth0 [fth1 [fth2 [fth3 fth4]]]]].

  (* to prove the n+2 left bound in between r1 and r2 *)
  pose proof (first_two_in_interval_works u v r1 r2 H H2).
  rewrite <- H5 in H6. destruct H6 as [H6 [H7 [H8 [H9 [H10 H11]]]]]. apply fth4.
  - apply (Rlt_trans r r1); assumption.
  - apply (Rlt_trans r3 r2); assumption.
  - intro abs. subst. apply Rlt_irrefl in H6. contradiction.
  - intro abs. subst. apply Rlt_irrefl in H7. contradiction.
Qed.

Theorem R_uncountable : forall u : nat -> R, ~Bijective u.
Proof.
  intros u [v [H3 H4]]. pose proof (conj H4 H3) as H.
  assert (forall n : nat, n + v (fst (proj1_sig (tearing_sequences u v H 1)))
                   <= v (fst (proj1_sig (tearing_sequences u v H (S n))))).
  { induction n. simpl. apply le_refl.
    apply (le_trans (S n + v (fst (proj1_sig (tearing_sequences u v H 1))))
                    (S (v (fst (proj1_sig (tearing_sequences u v H (S n))))))).
    simpl. apply le_n_S. assumption. apply first_indices_increasing.
    intro H1. discriminate. }
  assert (v (proj1_sig (torn_number u v H)) + v (fst (proj1_sig (tearing_sequences u v H 1)))
          < v (proj1_sig (torn_number u v H))).
  { pose proof (limit_index_above_all_indices u v H (v (proj1_sig (torn_number u v H)))).
    specialize (H0 (v (proj1_sig (torn_number u v H)))).
    apply (le_lt_trans (v (proj1_sig (torn_number u v H))
                        + v (fst (proj1_sig (tearing_sequences u v H 1))))
                       (v (fst (proj1_sig (tearing_sequences u v H (S (v (proj1_sig (torn_number u v H))))))))).
    assumption. assumption. }
  assert (forall n m : nat, ~(n + m < n)).
  { induction n. intros. intro H2. inversion H2. intro m. intro H2. simpl in H2.
    apply lt_pred in H2. simpl in H2. apply IHn in H2. contradiction. }
  apply H2 in H1. contradiction.
Qed.
