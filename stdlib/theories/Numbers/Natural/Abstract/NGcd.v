(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Properties of the greatest common divisor *)

Require Import NAxioms NSub NZGcd.

Module Type NGcdProp
 (Import A : NAxiomsSig')
 (Import B : NSubProp A).

Module Import Private_NZGcdProp := NZGcdProp A A B.

(** Properties of divide *)

#[global] Instance divide_wd : Proper (eq==>eq==>iff) divide := divide_wd.
Definition divide_1_r n := divide_1_r_nonneg n (le_0_l n).
Definition divide_1_l := divide_1_l.
Definition divide_0_r := divide_0_r.
Definition divide_0_l := divide_0_l.
Definition divide_refl := divide_refl.
Definition divide_trans := divide_trans.
#[global] Instance divide_reflexive : Reflexive divide | 5 := divide_refl.
#[global] Instance divide_transitive : Transitive divide | 5 := divide_trans.
Definition divide_antisym n m := divide_antisym_nonneg n m (le_0_l n) (le_0_l m).
Definition mul_divide_mono_l := mul_divide_mono_l.
Definition mul_divide_mono_r := mul_divide_mono_r.
Definition mul_divide_cancel_l := mul_divide_cancel_l.
Definition mul_divide_cancel_r := mul_divide_cancel_r.
Definition divide_add_r := divide_add_r.
Definition divide_mul_l := divide_mul_l.
Definition divide_mul_r := divide_mul_r.
Definition divide_factor_l := divide_factor_l.
Definition divide_factor_r := divide_factor_r.
Definition divide_pos_le := divide_pos_le.

(** Properties of gcd *)

Definition gcd_0_l n : gcd 0 n == n := gcd_0_l_nonneg n (le_0_l n).
Definition gcd_0_r n : gcd n 0 == n := gcd_0_r_nonneg n (le_0_l n).
Definition gcd_diag n : gcd n n == n := gcd_diag_nonneg n (le_0_l n).
Definition gcd_unique n m p := gcd_unique n m p (le_0_l p).
Definition gcd_unique_alt n m p := gcd_unique_alt n m p (le_0_l p).
Definition divide_gcd_iff n m := divide_gcd_iff n m (le_0_l n).
#[global] Instance gcd_wd : Proper (eq==>eq==>eq) gcd := gcd_wd.
Definition gcd_comm := gcd_comm.
Definition gcd_assoc := gcd_assoc.
Definition gcd_eq_0_l := gcd_eq_0_l.
Definition gcd_eq_0_r := gcd_eq_0_r.
Definition gcd_eq_0 := gcd_eq_0.
Definition gcd_mul_diag_l n m := gcd_mul_diag_l n m (le_0_l n).

#[deprecated(since="8.17",note="Use divide_antisym instead.")]
Notation divide_antisym_nonneg := divide_antisym_nonneg (only parsing).
#[deprecated(since="8.17",note="Use gcd_unique instead.")]
Notation gcd_unique' n m p := gcd_unique (only parsing).
#[deprecated(since="8.17",note="Use gcd_unique_alt instead.")]
Notation gcd_unique_alt' := gcd_unique_alt.
#[deprecated(since="8.17",note="Use divide_gcd_iff instead.")]
Notation divide_gcd_iff' := divide_gcd_iff.

Lemma divide_add_cancel_r : forall n m p, (n | m) -> (n | m + p) -> (n | p).
Proof.
 intros n m p (q,Hq) (r,Hr).
 exists (r-q). rewrite mul_sub_distr_r, <- Hq, <- Hr.
 now rewrite add_comm, add_sub.
Qed.

Lemma divide_sub_r : forall n m p, (n | m) -> (n | p) -> (n | m - p).
Proof.
 intros n m p H H'.
 destruct (le_ge_cases m p) as [LE|LE].
 - apply sub_0_le in LE. rewrite LE. apply divide_0_r.
 - apply divide_add_cancel_r with p; trivial.
   now rewrite add_comm, sub_add.
Qed.

Lemma gcd_add_mult_diag_r : forall n m p, gcd n (m+p*n) == gcd n m.
Proof.
 intros n m p. apply gcd_unique_alt.
 intros. rewrite gcd_divide_iff. split; intros (U,V); split; trivial.
 - apply divide_add_r; trivial. now apply divide_mul_r.
 - apply divide_add_cancel_r with (p*n); trivial.
   + now apply divide_mul_r.
   + now rewrite add_comm.
Qed.

Lemma gcd_add_diag_r : forall n m, gcd n (m+n) == gcd n m.
Proof.
 intros n m. rewrite <- (mul_1_l n) at 2. apply gcd_add_mult_diag_r.
Qed.

Lemma gcd_sub_diag_r : forall n m, n<=m -> gcd n (m-n) == gcd n m.
Proof.
 intros n m H. symmetry.
 rewrite <- (sub_add n m H) at 1. apply gcd_add_diag_r.
Qed.

(** On natural numbers, we should use a particular form
  for the Bezout identity, since we don't have full subtraction. *)

Definition Bezout n m p := exists a b, a*n == p + b*m.

#[global]
Instance Bezout_wd : Proper (eq==>eq==>eq==>iff) Bezout.
Proof.
 unfold Bezout. intros x x' Hx y y' Hy z z' Hz.
 setoid_rewrite Hx. setoid_rewrite Hy. now setoid_rewrite Hz.
Qed.

Lemma bezout_1_gcd : forall n m, Bezout n m 1 -> gcd n m == 1.
Proof.
 intros n m (q & r & H).
 apply gcd_unique; trivial using divide_1_l, le_0_1.
 intros p Hn Hm.
 apply divide_add_cancel_r with (r*m).
 - now apply divide_mul_r.
 - rewrite add_comm, <- H. now apply divide_mul_r.
Qed.

(** Bezout on natural numbers commutes *)

Theorem bezout_comm : forall a b g,
  b ~= 0 -> Bezout a b g -> Bezout b a g.
Proof.
  intros a b g Hb [p [q Hpq]].
  destruct (eq_decidable a 0) as [Ha|Ha].
  { exists 0, 0. symmetry in Hpq.
    rewrite Ha, mul_0_r in Hpq.
    apply eq_add_0 in Hpq as [-> _].
    now nzsimpl. }
  exists (a*(p+1)*(q+1)-q), (b*(p+1)*(q+1)-p).
  enough (E' : (a*(p+1)*(q+1)-q+q)*b == (b*(p+1)*(q+1)-p+p)*a).
  { rewrite (mul_add_distr_r _ _ a), (mul_add_distr_r _ _ b), Hpq in E'.
    rewrite add_assoc, (add_comm _ g) in E'.
    now apply add_cancel_r in E'. }
  rewrite !sub_add.
  - now rewrite !(mul_comm _ b), !mul_assoc, !(mul_comm _ a), !mul_assoc.
  - rewrite <- mul_1_r at 1. apply mul_le_mono; [|apply le_add_l].
    rewrite <- mul_1_l at 1. apply mul_le_mono; [|apply le_add_r].
    rewrite one_succ. apply le_succ_l. assert (H := le_0_l b). order.
  - rewrite <- mul_1_l at 1. apply mul_le_mono; [|apply le_add_r].
    rewrite <- mul_1_l at 1. apply mul_le_mono; [|apply le_add_l].
    rewrite one_succ. apply le_succ_l. assert (H := le_0_l a). order.
Qed.

Lemma gcd_bezout_pos : forall n m, 0 < n -> Bezout n m (gcd n m).
Proof.
  enough (H : forall nm, 0 < fst nm -> Bezout (fst nm) (snd nm) (gcd (fst nm) (snd nm))).
  { intros n m. apply (H (n, m)). }
  intros nm.
  induction nm as [[n m] IH] using (measure_induction _ (fun '(n, m) => n + m)).
  enough (H : forall n' m', n+m == n'+m' -> 0<n'<m' -> Bezout n' m' (gcd n' m')).
  { cbn. intros ?. destruct (lt_trichotomy n m) as [Hnm|[Hnm|Hnm]].
    - now apply H.
    - exists 1, 0. now rewrite Hnm, mul_1_l, mul_0_l, add_0_r, gcd_diag.
    - destruct (eq_0_gt_0_cases m) as [->|?].
      + exists 1, 0. now rewrite gcd_0_r, mul_1_l, mul_0_l, add_0_r.
      + apply bezout_comm; [order|].
        rewrite gcd_comm. now apply H; [apply add_comm|]. }
  intros n' m' E' [Hn' Hn'm'].
  assert (Hlt : n' + (m' - n') < n + m).
  { rewrite (add_comm n'), E', sub_add by order.
    now apply lt_add_pos_l. }
  destruct (IH (n', m'-n') Hlt Hn') as [a [b Hab]].
  cbn in Hab. exists (a+b), b.
  rewrite mul_add_distr_r, Hab, mul_sub_distr_l, gcd_sub_diag_r by order.
  now rewrite <- add_assoc, sub_add by (apply mul_le_mono_l; order).
Qed.

(** For strictly positive numbers, we have Bezout in the two directions. *)

Lemma gcd_bezout_pos_pos : forall n, 0<n -> forall m, 0<m ->
 Bezout n m (gcd n m) /\ Bezout m n (gcd n m).
Proof.
 intros ????. split; [|rewrite gcd_comm]; now apply gcd_bezout_pos.
Qed.

(** For arbitrary natural numbers, we could only say that at least
  one of the Bezout identities holds. *)

Lemma gcd_bezout : forall n m,
 Bezout n m (gcd n m) \/ Bezout m n (gcd n m).
Proof.
 intros n m.
 destruct (eq_0_gt_0_cases n) as [EQ|LT].
 - right. rewrite EQ, gcd_0_l. exists 1. exists 0. now nzsimpl.
 - left. now apply gcd_bezout_pos.
Qed.

Lemma gcd_mul_mono_l :
  forall n m p, gcd (p * n) (p * m) == p * gcd n m.
Proof.
  intros n m p. apply gcd_unique.
  - apply mul_divide_mono_l, gcd_divide_l.
  - apply mul_divide_mono_l, gcd_divide_r.
  - intros q H H'.
    destruct (eq_0_gt_0_cases n) as [EQ|LT].
    + rewrite EQ in *. now rewrite gcd_0_l.
    + destruct (gcd_bezout_pos n m) as (a & b & EQ); trivial.
      apply divide_add_cancel_r with (p*m*b).
      * now apply divide_mul_l.
      * rewrite <- mul_assoc, <- mul_add_distr_l, add_comm, (mul_comm m), <- EQ.
        rewrite (mul_comm a), mul_assoc.
        now apply divide_mul_l.
Qed.

Lemma gcd_mul_mono_r :
 forall n m p, gcd (n*p) (m*p) == gcd n m * p.
Proof.
 intros n m p. rewrite !(mul_comm _ p). apply gcd_mul_mono_l.
Qed.

Lemma gauss : forall n m p, (n | m * p) -> gcd n m == 1 -> (n | p).
Proof.
 intros n m p H G.
 destruct (eq_0_gt_0_cases n) as [EQ|LT].
 - rewrite EQ in *. rewrite gcd_0_l in G. now rewrite <- (mul_1_l p), <- G.
 - destruct (gcd_bezout_pos n m) as (a & b & EQ); trivial.
   rewrite G in EQ.
   apply divide_add_cancel_r with (m*p*b).
   + now apply divide_mul_l.
   + rewrite (mul_comm _ b), mul_assoc. rewrite <- (mul_1_l p) at 2.
     rewrite <- mul_add_distr_r, add_comm, <- EQ.
     now apply divide_mul_l, divide_factor_r.
Qed.

Lemma divide_mul_split : forall n m p, n ~= 0 -> (n | m * p) ->
 exists q r, n == q*r /\ (q | m) /\ (r | p).
Proof.
 intros n m p Hn H.
 assert (G := gcd_nonneg n m). le_elim G.
 - destruct (gcd_divide_l n m) as (q,Hq).
   exists (gcd n m). exists q.
   split.
   + now rewrite mul_comm.
   + split.
     * apply gcd_divide_r.
     * destruct (gcd_divide_r n m) as (r,Hr).
       rewrite Hr in H. rewrite Hq in H at 1.
       rewrite mul_shuffle0 in H. apply mul_divide_cancel_r in H; [|order].
       apply gauss with r; trivial.
       apply mul_cancel_r with (gcd n m); [order|].
       rewrite mul_1_l.
       rewrite <- gcd_mul_mono_r, <- Hq, <- Hr; order.
 - symmetry in G. apply gcd_eq_0 in G. destruct G as (Hn',_); order.
Qed.

(** TODO : relation between gcd and division and modulo *)

(** TODO : more about rel_prime (i.e. gcd == 1), about prime ... *)

End NGcdProp.
