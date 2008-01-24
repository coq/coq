(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module proves the decidablitiy of arithmetical statements from
the axiom that the order of the real numbers is decidable. *)

(** Assuming a decidable predicate [P n], A series is constructied who's
[n]th term is 1/2^n if [P n] holds and 0 otherwise.  This sum reaches 2
only if [P n] holds for all [n], otherwise the sum is less than 2.
Comparing the sum to 2 decides if [forall n, P n] or [~forall n, P n] *)

(** One can iterate this lemma and use classical logic to decide any
statement in the arithmetical heirarchy. *)

(** Contributed by Cezary Kaliszyk and Russell O'Connor *)

Require Import ConstructiveEpsilon.
Require Import Reals.
Require Import Fourier.
 
Section Arithmetical_dec.

Variable P : nat -> Prop.
Hypothesis HP : forall n, {P n} + {~P n}.

Let positive_sums_lemma : (forall (m n : nat) (f : nat -> R), (lt m n) -> (forall i : nat, 0 <= f i) -> sum_f_R0 f m <= sum_f_R0 f n).
intros m n f mn fpos.
replace (sum_f_R0 f m) with (sum_f_R0 f m + 0) by ring.
rewrite (tech2 f m n mn).
assert (sum_f_R0 f m = sum_f_R0 f m + 0) by ring.
apply Rplus_le_compat_l.
induction (n - S m)%nat.
 simpl.
 apply fpos.
simpl in *.
replace 0 with (0 + 0) by ring.
apply (Rplus_le_compat _ _ _ _ IHn0 (fpos (S (m + S n0)%nat))).
Qed.

Let positive_sums : (forall (m n : nat) (f : nat -> R), (le m n) -> (forall i : nat, 0 <= f i) -> sum_f_R0 f m <= sum_f_R0 f n).
intros m n f mn pos.
elim (le_lt_or_eq _ _ mn).
intro; apply positive_sums_lemma; assumption.
intro H; rewrite H; auto with *.
Qed.

Lemma forall_dec : {forall n, P n} + {~forall n, P n}.
Proof.
set (f:=fun n => (if HP n then (1/2)^n else 0)%R).
 assert (Hg:Cauchy_crit_series f).
 intros e He.
 assert (X:(Pser (fun n:nat => 1) (1/2) (/ (1 - (1/2))))%R).
  apply GP_infinite.
  apply Rabs_def1; fourier.
 assert (He':e/2 > 0) by fourier.
 destruct (X _ He') as [N HN].
 clear X.
 exists N.
 intros n m Hn Hm.
 replace e with (e/2 + e/2)%R by fourier.
 set (g:=(fun n0 : nat => 1 * (1 / 2) ^ n0)) in *.
 assert (R_dist (sum_f_R0 g n) (sum_f_R0 g m) < e / 2 + e / 2).
  apply Rle_lt_trans with (R_dist (sum_f_R0 g n) 2+R_dist 2 (sum_f_R0 g m))%R.
   apply R_dist_tri.
  replace (/(1 - 1/2)) with 2 in HN by fourier.
  cut (forall n, (n >= N)%nat -> R_dist (sum_f_R0 g n) 2 < e/2)%R.
   intros Z.
   apply Rplus_lt_compat.
    apply Z; assumption.
   rewrite R_dist_sym.
   apply Z; assumption.
  clear - HN He.
  intros n Hn.
  apply HN.
  auto.
 eapply Rle_lt_trans;[|apply H].
 clear -positive_sums n.
 cut (forall n m, (m <= n)%nat -> R_dist (sum_f_R0 f n) (sum_f_R0 f m) <= R_dist (sum_f_R0 g n) (sum_f_R0 g m)).
  intros H.
  destruct (le_lt_dec m n).
   apply H; assumption.
  rewrite R_dist_sym.
  rewrite (R_dist_sym (sum_f_R0 g n)).
  apply H; auto with *.
 clear n m.
 intros n m Hnm.
 unfold R_dist.
 cut (forall i : nat, (1 / 2) ^ i >= 0). intro RPosPow.
 rewrite Rabs_pos_eq.
  rewrite Rabs_pos_eq.
   cut (sum_f_R0 g m - sum_f_R0 f m <=  sum_f_R0 g n - sum_f_R0 f n).
    intros; fourier.
   do 2 rewrite <- minus_sum.
 apply (positive_sums m n (fun i : nat => g i - f i) Hnm).
 intro i.
 unfold f, g.
 elim (HP i); intro; ring_simplify; auto with *.
 cut (sum_f_R0 g m <= sum_f_R0 g n). intro; fourier.
 apply (positive_sums m n g Hnm).
 intro. unfold g.
 ring_simplify.
 apply Rge_le.
 apply RPosPow.
 cut (sum_f_R0 f m <= sum_f_R0 f n). intro; fourier.
 apply (positive_sums m n f Hnm).
 intro; unfold f.
 elim (HP i); intro; simpl.
 apply Rge_le.
 apply RPosPow.
 auto with *.
 induction i.
 simpl. apply Rle_ge. auto with *.
 simpl. fourier.

 destruct (cv_cauchy_2 _ Hg).
 cut (2 <= x <-> forall n : nat, P n).
 intro H.
 elim (Rle_dec 2 x); intro X.
 left; tauto.
 right; tauto.

 assert (A:Rabs(1/2) < 1) by (apply Rabs_def1; fourier).
 assert (A0:=(GP_infinite (1/2) A)).
 symmetry.
 split; intro.
 replace 2 with (/ (1 - (1 / 2))) by field.
 unfold Pser, infinit_sum in A0.
 eapply Rle_cv_lim;[|unfold Un_cv; apply A0 |apply u].
 intros n.
 clear -n H.
 induction n; unfold f;simpl.
  destruct (HP 0); auto with *.
  elim n; auto.
 apply Rplus_le_compat; auto.
 destruct (HP (S n)); auto with *.
 elim n0; auto.

intros n.
destruct (HP n); auto.
elim (RIneq.Rle_not_lt _ _ H).
assert (B:0< (1/2)^n).
 apply pow_lt.
 fourier.
apply Rle_lt_trans with (2-(1/2)^n);[|fourier].
replace (/(1-1/2))%R with 2 in A0 by field.
set (g:= fun m => if (eq_nat_dec m n) then (1/2)^n else 0).
assert (Z:  Un_cv (fun N : nat => sum_f_R0 g N) ((1/2)^n)).
 intros e He.
 exists n.
 intros a Ha.
 replace (sum_f_R0 g a) with ((1/2)^n).
  rewrite (R_dist_eq); assumption.
 symmetry.
 cut (forall a : nat, ((a >= n)%nat -> sum_f_R0 g a = (1 / 2) ^ n) /\ ((a < n)%nat -> sum_f_R0 g a = 0))%R.
  intros H0.
  destruct (H0 a).
  auto.
 clear - g.
 induction a.
  split;
   intros H;
   simpl; unfold g;
   destruct (eq_nat_dec 0 n); try reflexivity.
   elim f; auto with *.
  elimtype False; omega.
 destruct IHa as [IHa0 IHa1].
 split;
  intros H;
  simpl; unfold g at 2;
  destruct (eq_nat_dec (S a) n).
   rewrite IHa1.
    ring.
   omega.
  ring_simplify.
  apply IHa0.
  omega.
  elimtype False; omega.
 ring_simplify.
 apply IHa1.
 omega.
assert (C:=CV_minus _ _ _ _ A0 Z).
eapply Rle_cv_lim;[|apply u |apply C].
clear - n0 B.
intros m.
simpl.
induction m.
 simpl.
 unfold f, g.
 destruct (eq_nat_dec 0 n).
  destruct (HP 0).
   elim n0.
   congruence.
  clear -n.
  induction n; simpl; fourier.
 destruct (HP); simpl; fourier.
cut (f (S m) <= 1 * ((1 / 2) ^ (S m)) - g (S m)).
 intros L.
 eapply Rle_trans.
  simpl.
  apply Rplus_le_compat.
   apply IHm.
  apply L.
 simpl; fourier.
unfold f, g.
destruct (eq_nat_dec (S m) n).
 destruct (HP (S m)).
  elim n0.
  congruence.
 rewrite e.
 fourier.
destruct (HP (S m)).
 fourier.
ring_simplify.
apply pow_le.
fourier.
Qed.

Lemma sig_forall_dec :  {n | ~P n}+{forall n, P n}.
destruct forall_dec.
 right; assumption.
left.
apply constructive_indefinite_description_nat; auto.
 clear - HP.
 firstorder.
apply Classical_Pred_Type.not_all_ex_not.
assumption.
Qed.

End Arithmetical_dec.
