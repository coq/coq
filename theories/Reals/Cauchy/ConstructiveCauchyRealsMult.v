(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(************************************************************************)

(** The multiplication and division of Cauchy reals.

    WARNING: this file is experimental and likely to change in future releases.
*)

Require Import QArith Qabs Qround Qpower.
Require Import Logic.ConstructiveEpsilon.
Require Export ConstructiveCauchyReals.
Require CMorphisms.
Require Import Znat.
Require Import Zorder.
Require Import Lia.
Require Import Lqa.
Require Import QExtra.

Local Open Scope CReal_scope.

Definition CReal_mult_seq (x y : CReal) :=
  (fun n : Z => seq x (n - scale y - 1)%Z
              * seq y (n - scale x - 1)%Z).

Definition CReal_mult_scale (x y : CReal) : Z :=
  x.(scale) + y.(scale).

Local Ltac simplify_Qpower_exponent :=
  match goal with |- context [(_ ^ ?a)%Q] => ring_simplify a end.

Local Ltac simplify_Qabs :=
  match goal with |- context [(Qabs ?a)%Q] => ring_simplify a end.

Local Ltac simplify_Qabs_in H :=
  match type of H with context [(Qabs ?a)%Q] => ring_simplify a in H end.

Local Ltac field_simplify_Qabs :=
  match goal with |- context [(Qabs ?a)%Q] => field_simplify a end.

Local Ltac pose_Qabs_pos :=
  match goal with |- context [(Qabs ?a)%Q] => pose proof Qabs_nonneg a end.

Local Ltac simplify_Qle :=
  match goal with |- (?l <= ?r)%Q => ring_simplify l; ring_simplify r end.

Local Ltac simplify_Qle_in H :=
  match type of H with (?l <= ?r)%Q => ring_simplify l in H; ring_simplify r in H end.

Local Ltac simplify_Qlt :=
  match goal with |- (?l < ?r)%Q => ring_simplify l; ring_simplify r end.

Local Ltac simplify_Qlt_in H :=
  match type of H with (?l < ?r)%Q => ring_simplify l in H; ring_simplify r in H end.

Local Ltac simplify_seq_idx :=
  match goal with |- context [seq ?x ?n] => progress ring_simplify n end.

Local Lemma Weaken_Qle_QpowerAddExp: forall (q : Q) (n m : Z),
    (m >= 0)%Z
 -> (q <= 2^n)%Q
 -> (q <= 2^(n+m))%Q.
Proof.
  intros q n m Hmpos Hle.
  pose proof Qpower_le_compat_l 2 n (n+m) ltac:(lia) ltac:(lra).
  lra.
Qed.

Local Lemma Weaken_Qle_QpowerRemSubExp: forall (q : Q) (n m : Z),
    (m >= 0)%Z
 -> (q <= 2^(n-m))%Q
 -> (q <= 2^n)%Q.
Proof.
  intros q n m Hmpos Hle.
  pose proof Qpower_le_compat_l 2 (n-m) n ltac:(lia) ltac:(lra).
  lra.
Qed.

Local Lemma Weaken_Qle_QpowerFac: forall (q r : Q) (n : Z),
    (r >= 1)%Q
 -> (q <= 2^n)%Q
 -> (q <= r * 2^n)%Q.
Proof.
  intros q r n Hrge1 Hle.
  rewrite <- (Qmult_1_l (2^n)%Q) in Hle.
  pose proof Qmult_le_compat_r 1 r (2^n)%Q Hrge1 (Qpower_pos 2 n ltac:(lra)) as Hpow.
  lra.
Qed.

Lemma CReal_mult_cauchy: forall (x y : CReal),
  QCauchySeq (CReal_mult_seq x y).
Proof.
  intros x y n p q Hp Hq.
  unfold CReal_mult_seq.

  assert(forall xp xq yp yq : Q, xp * yp - xq * yq == (xp - xq) * yp + xq * (yp - yq))%Q
    as H by (intros; ring).
  rewrite H; clear H.

  apply (Qle_lt_trans _ _ _ (Qabs_triangle _ _)).
  do 2 rewrite Qabs_Qmult.

  replace n with ((n-1)+1)%Z by ring.
  rewrite Qpower_plus by lra.
  setoid_replace (2 ^ (n - 1) * 2 ^1)%Q with (2 ^ (n - 1) + 2 ^ (n - 1))%Q by ring.

  apply Qplus_lt_le_compat.
  - apply (Qle_lt_trans _ ((2 ^ (n - scale y - 1)) * Qabs (seq y (p - scale x - 1)))).
    + apply Qmult_le_compat_r.
        2: apply Qabs_nonneg.
      apply Qlt_le_weak. apply (cauchy x); lia.
    + apply (Qmult_lt_l _ _ (2 ^ -(n - scale y - 1))%Q).
      { apply Qpower_0_lt; lra. }
      rewrite Qmult_assoc, <- Qpower_plus by lra.
      rewrite <- Qpower_plus by lra.
      simplify_Qpower_exponent; rewrite Qpower_0_r, Qmult_1_l.
      simplify_Qpower_exponent.
      apply (bound y).
  - apply Qlt_le_weak.
    apply (Qle_lt_trans _ ((2 ^ (n - scale x - 1)) * Qabs (seq x (q - scale y - 1)))).
    + rewrite Qmult_comm; apply Qmult_le_compat_r.
        2: apply Qabs_nonneg.
      apply Qlt_le_weak; apply (cauchy y); lia.
    + apply (Qmult_lt_l _ _ (2 ^ -(n - scale x - 1))%Q).
      { apply Qpower_0_lt; lra. }
      rewrite Qmult_assoc, <- Qpower_plus by lra.
      rewrite <- Qpower_plus by lra.
      simplify_Qpower_exponent; rewrite Qpower_0_r, Qmult_1_l.
      simplify_Qpower_exponent.
      apply (bound x).
Qed.

Lemma CReal_mult_bound : forall (x y : CReal),
  QBound (CReal_mult_seq x y) (CReal_mult_scale x y).
Proof.
  intros x y k.
  unfold CReal_mult_seq, CReal_mult_scale.
  pose proof (bound x (k - scale y - 1)%Z) as Hxbnd.
  pose proof (bound y (k - scale x - 1)%Z) as Hybnd.
  pose proof Qabs_nonneg (seq x (k - scale y - 1)) as Habsx.
  pose proof Qabs_nonneg (seq y (k - scale x - 1)) as Habsy.
  rewrite Qabs_Qmult; rewrite Qpower_plus by lra.
  apply Qmult_lt_compat_nonneg; lra.
Qed.

Definition CReal_mult (x y : CReal) : CReal :=
{|
  seq := CReal_mult_seq x y;
  scale := CReal_mult_scale x y;
  cauchy := CReal_mult_cauchy x y;
  bound := CReal_mult_bound x y
|}.

Infix "*" := CReal_mult : CReal_scope.

Lemma CReal_mult_comm : forall x y : CReal, x * y == y * x.
Proof.
  assert (forall x y : CReal, x * y <= y * x) as H.
  { intros x y [n nmaj]. apply (Qlt_not_le _ _ nmaj). clear nmaj.
    unfold CReal_mult, CReal_mult_seq; do 2 rewrite CReal_red_seq.
    ring_simplify.
    pose proof Qpower_0_lt 2 n ltac:(lra); lra. }
  split; apply H.
Qed.

(* ToDo: make a tactic for this *)
Lemma CReal_red_scale: forall (a : Z -> Q) (b : Z) (c : QCauchySeq a) (d : QBound a b),
  scale (mkCReal a b c d) = b.
Proof.
  reflexivity.
Qed.

Lemma CReal_mult_proper_0_l : forall x y : CReal,
    y == 0 -> x * y == 0.
Proof.
  intros x y Hyeq0.

  apply CRealEq_diff; intros n.
  unfold CReal_mult, CReal_mult_seq, inject_Q; do 2 rewrite CReal_red_seq.
  simplify_Qabs.

  rewrite CRealEq_diff in Hyeq0.
  unfold inject_Q in Hyeq0; rewrite CReal_red_seq in Hyeq0.
  specialize (Hyeq0 (n - scale x - 1)%Z).
  simplify_Qabs_in Hyeq0.
  rewrite Qpower_minus_pos in Hyeq0 by lra; simplify_Qle_in Hyeq0.

  pose proof bound x (n - scale y - 1)%Z as Hxbnd.
  apply Weaken_Qle_QpowerFac; [lra|].

  (* Now split the power of 2 and solve the goal*)
  replace n with ((scale x) + (n - scale x))%Z at 3 by ring.
  rewrite Qpower_plus by lra.
  rewrite Qabs_Qmult.
  apply Qmult_le_compat_nonneg;
    (pose_Qabs_pos; lra).
Qed.

Lemma CReal_mult_0_r : forall r, r * 0 == 0.
Proof.
  intros. apply CReal_mult_proper_0_l. reflexivity.
Qed.

Lemma CReal_mult_0_l : forall r, 0 * r == 0.
Proof.
  intros. rewrite CReal_mult_comm. apply CReal_mult_0_r.
Qed.

Lemma CReal_scale_sep0_limit : forall (x : CReal) (n : Z),
    (2 * (2^n)%Q < seq x n)%Q
 -> (n <= scale x - 2)%Z.
Proof.
  intros x n Hnx.
  pose proof bound x n as Hxbnd.
  apply Qabs_Qlt_condition in Hxbnd.
  destruct Hxbnd as [_ Hxbnd].
  apply (Qlt_trans _ _ _ Hnx) in Hxbnd.
  replace n with ((n+1)-1)%Z in Hxbnd by lia.
  rewrite Qpower_minus_pos in Hxbnd by lra.
  simplify_Qlt_in Hxbnd.
  apply (Qpower_lt_compat_l_inv) in Hxbnd.
  - lia.
  - lra.
Qed.

(* Correctness lemma for the Definition CReal_mult_lt_0_compat below. *)
Lemma CReal_mult_lt_0_compat_correct
  : forall (x y : CReal) (Hx : 0 < x) (Hy : 0 < y),
    (2 * 2^(proj1_sig Hx + proj1_sig Hy - 1)%Z <
     seq (x * y)%CReal (proj1_sig Hx + proj1_sig Hy - 1)%Z -
     seq (inject_Q 0) (proj1_sig Hx + proj1_sig Hy - 1)%Z)%Q.
Proof.
  intros x y Hx Hy.
  destruct Hx as [nx Hx], Hy as [ny Hy]; unfold proj1_sig.
  unfold inject_Q, Qminus in Hx. rewrite CReal_red_seq, Qplus_0_r in Hx.
  unfold inject_Q, Qminus in Hy. rewrite CReal_red_seq, Qplus_0_r in Hy.

  unfold CReal_mult, CReal_mult_seq, inject_Q; do 2 rewrite CReal_red_seq.
  rewrite Qpower_minus_pos by lra.
  rewrite Qpower_plus by lra.
  simplify_Qlt.
  do 2 simplify_seq_idx.
  apply Qmult_lt_compat_nonneg.
  - split.
    + pose proof Qpower_0_lt 2 nx; lra.
    + pose proof CReal_scale_sep0_limit y ny Hy as Hlimy.
      pose proof cauchy x nx nx (nx + ny - scale y - 2)%Z ltac:(lia) ltac:(lia) as Hbndx.
      apply Qabs_Qlt_condition in Hbndx.
      lra.
  - split.
    + pose proof Qpower_0_lt 2 ny; lra.
    + pose proof CReal_scale_sep0_limit x nx Hx as Hlimx.
      pose proof cauchy y ny ny (nx + ny - scale x - 2)%Z ltac:(lia) ltac:(lia) as Hbndy.
      apply Qabs_Qlt_condition in Hbndy.
      lra.
Qed.

(* Strict inequality on CReal is in sort Type, for example
   used in the computation of division. *)
Definition CReal_mult_lt_0_compat : forall x y : CReal,
    0 < x -> 0 < y -> 0 < x * y
  := fun x y Hx Hy => exist _ (proj1_sig Hx + proj1_sig Hy - 1)%Z
                        (CReal_mult_lt_0_compat_correct
                           x y Hx Hy).

Lemma CReal_mult_plus_distr_l : forall r1 r2 r3 : CReal,
    r1 * (r2 + r3) == (r1 * r2) + (r1 * r3).
Proof.
  intros x y z; apply CRealEq_diff; intros n.
  unfold CReal_mult, CReal_mult_seq, CReal_mult_scale, CReal_plus, CReal_plus_seq, CReal_plus_scale.
  do 5 rewrite CReal_red_seq.
  do 1 rewrite CReal_red_scale.
  do 2 rewrite Qred_correct.
  do 5 simplify_seq_idx.
  simplify_Qabs.
  assert (forall y' z': CReal,
    Qabs (
      seq x (n - Z.max (scale y') (scale z') - 2) * seq y' (n - scale x - 2)
    - seq x (n - scale y' - 2) * seq y' (n - scale x - 2))
  <= 2 ^ n )%Q as Hdiffbnd.
  {
    intros y' z'.
    assert (forall a b c : Q, a*c-b*c==(a-b)*c)%Q as H by (intros; ring).
    rewrite H; clear H.
    pose proof cauchy x (n - (scale y') - 2)%Z (n - Z.max (scale y') (scale z') - 2)%Z (n - scale y' - 2)%Z
      ltac:(lia) ltac:(lia) as Hxbnd.
    pose proof bound y' (n - scale x - 2)%Z as Hybnd.
    replace n with ((n - scale y' - 2) + scale y' + 2)%Z at 4 by lia.
    apply Weaken_Qle_QpowerAddExp.
    { lia. }
    rewrite Qpower_plus, Qabs_Qmult by lra.
    apply Qmult_le_compat_nonneg; (split; [apply Qabs_nonneg | lra]).
  }
  pose proof Hdiffbnd y z as Hyz.
  pose proof Hdiffbnd z y as Hzy; clear Hdiffbnd.
  pose proof Qplus_le_compat _ _ _ _ Hyz Hzy as Hcomb; clear Hyz Hzy.
  apply (Qle_trans _ _ _ (Qabs_triangle _ _)) in Hcomb.
  rewrite (Z.max_comm (scale z) (scale y)) in Hcomb .
  rewrite Qabs_Qle_condition in Hcomb |- *.
  lra.
Qed.

Lemma CReal_mult_plus_distr_r : forall r1 r2 r3 : CReal,
    (r2 + r3) * r1 == (r2 * r1) + (r3 * r1).
Proof.
  intros.
  rewrite CReal_mult_comm, CReal_mult_plus_distr_l,
  <- (CReal_mult_comm r1), <- (CReal_mult_comm r1).
  reflexivity.
Qed.

Lemma CReal_opp_mult_distr_r
  : forall r1 r2 : CReal, - (r1 * r2) == r1 * (- r2).
Proof.
  intros. apply (CReal_plus_eq_reg_l (r1*r2)).
  rewrite CReal_plus_opp_r, <- CReal_mult_plus_distr_l.
  symmetry. apply CReal_mult_proper_0_l.
  apply CReal_plus_opp_r.
Qed.

Lemma CReal_mult_proper_l : forall x y z : CReal,
    y == z -> x * y == x * z.
Proof.
  intros. apply (CReal_plus_eq_reg_l (-(x*z))).
  rewrite CReal_plus_opp_l, CReal_opp_mult_distr_r.
  rewrite <- CReal_mult_plus_distr_l.
  apply CReal_mult_proper_0_l. rewrite H. apply CReal_plus_opp_l.
Qed.

Lemma CReal_mult_proper_r : forall x y z : CReal,
    y == z -> y * x == z * x.
Proof.
  intros. rewrite CReal_mult_comm, (CReal_mult_comm z).
  apply CReal_mult_proper_l, H.
Qed.

Lemma CReal_mult_assoc : forall x y z : CReal,
  (x * y) * z == x * (y * z).
Proof.
  intros x y z; apply CRealEq_diff; intros n.

  (* Expand and simplify the goal *)
  unfold CReal_mult, CReal_mult_seq, CReal_mult_scale.
  do 4 rewrite CReal_red_seq.
  do 2 rewrite CReal_red_scale.
  do 6 simplify_seq_idx.
  (* Todo: it is a bug in ring_simplify that the scales are not sorted *)
  replace (n - scale z - scale y)%Z with (n - scale y - scale z)%Z by ring.
  replace (n - scale z - scale x)%Z with (n - scale x - scale z)%Z by ring.
  simplify_Qabs.

  (* Rearrange the goal such that it used only scale and cauchy bounds *)
  (* Todo: it is also a bug in ring_simplify that the seq terms are not sorted by the first variable *)
  assert (forall a1 a2 b c1 c2 : Q, a1*b*c1+(-1)*b*a2*c2==(a1*c1-a2*c2)*b)%Q as H by (intros; ring).
  rewrite H; clear H.
  remember (seq x (n - scale y - scale z - 1) - seq x (n - scale y - scale z - 2))%Q as dx eqn:Heqdx.
  remember (seq z (n - scale x - scale y - 1) - seq z (n - scale x - scale y - 2))%Q as dz eqn:Heqdz.
  setoid_replace (seq x (n - scale y - scale z - 1)) with (seq x (n - scale y - scale z - 2) + dx)%Q
    by (rewrite Heqdx; ring).
  setoid_replace (seq z (n - scale x - scale y - 1)) with (seq z (n - scale x - scale y - 2) + dz)%Q
    by (rewrite Heqdz; ring).
  match goal with |- (Qabs (?a * _) <= _)%Q => ring_simplify a end.

  (* Now pose the scale and cauchy bounds we need to prove this, so that we see how to split the deviation budget *)
  pose proof bound x (n - scale y - scale z - 2)%Z as Hbndx.
  pose proof bound z (n - scale x - scale y - 2)%Z as Hbndz.
  pose proof bound y (n - scale x - scale z - 2)%Z as Hbndy.
  pose proof cauchy x (n - scale y - scale z - 1)%Z (n - scale y - scale z - 1)%Z (n - scale y - scale z - 2)%Z
    ltac:(lia) ltac:(lia) as Hbnddx; rewrite <- Heqdx in Hbnddx; clear Heqdx.
  pose proof cauchy z (n - scale x - scale y - 1)%Z (n - scale x - scale y - 1)%Z (n - scale x - scale y - 2)%Z
    ltac:(lia) ltac:(lia) as Hbnddz; rewrite <- Heqdz in Hbnddz; clear Heqdz.

  (* The rest is elementary arithmetic ... *)
  rewrite Qabs_Qmult.
  replace n with ((n - scale y) + scale y)%Z at 4 by lia.
  rewrite Qpower_plus by lra.
  rewrite Qmult_assoc.
  apply Qmult_le_compat_nonneg.
    2: (split; [apply Qabs_nonneg | lra]).

  split; [apply Qabs_nonneg|].
  apply (Qle_trans _ _ _ (Qabs_triangle _ _)).
  setoid_replace (2 * 2 ^ (n - scale y))%Q with (2 ^ (n - scale y) + 2 ^ (n - scale y))%Q by ring.
  apply Qplus_le_compat.
  - rewrite Qabs_Qmult.
    replace (n - scale y)%Z with (scale x + (n - scale x - scale y))%Z at 2 by lia.
    rewrite Qpower_plus by lra.
    apply Qmult_le_compat_nonneg.
    + (split; [apply Qabs_nonneg | lra]).
    + split; [apply Qabs_nonneg|].
      apply (Weaken_Qle_QpowerRemSubExp _ _ 1 ltac:(lia)), Qlt_le_weak, Hbnddz.
  - rewrite Qabs_Qmult.
    replace (n - scale y)%Z with (scale z + (n - scale y - scale z))%Z by lia.
    rewrite Qpower_plus by lra.
    apply Qmult_le_compat_nonneg.
    + split; [apply Qabs_nonneg|].
      rewrite <- Qabs_opp; simplify_Qabs; lra.
    + split; [apply Qabs_nonneg|].
      apply (Weaken_Qle_QpowerRemSubExp _ _ 1 ltac:(lia)), Qlt_le_weak, Hbnddx.
Qed.

Lemma CReal_mult_1_l : forall r: CReal,
  1 * r == r.
Proof.
  intros r; apply CRealEq_diff; intros n.

  unfold inject_Q, CReal_mult, CReal_mult_seq, CReal_mult_scale.
  do 2 rewrite CReal_red_seq.
  do 1 rewrite CReal_red_scale.
  change (Qbound_ltabs_ZExp2 1)%Z with 1%Z.
  do 1 simplify_seq_idx.
  simplify_Qabs.

  pose proof cauchy r n (n-2)%Z n ltac:(lia) ltac:(lia) as Hrbnd.
  apply Qabs_Qlt_condition in Hrbnd.
  apply Qabs_Qle_condition.
  lra.
Qed.

Lemma CReal_isRingExt : ring_eq_ext CReal_plus CReal_mult CReal_opp CRealEq.
Proof.
  split.
  - intros x y H z t H0. apply CReal_plus_morph; assumption.
  - intros x y H z t H0. apply (CRealEq_trans _ (CReal_mult x t)).
    + apply CReal_mult_proper_l. apply H0.
    + apply (CRealEq_trans _ (CReal_mult t x)). { apply CReal_mult_comm. }
      apply (CRealEq_trans _ (CReal_mult t y)).
      * apply CReal_mult_proper_l. apply H.
      * apply CReal_mult_comm.
  - intros x y H. apply (CReal_plus_eq_reg_l x).
    apply (CRealEq_trans _ (inject_Q 0)). { apply CReal_plus_opp_r. }
    apply (CRealEq_trans _ (CReal_plus y (CReal_opp y))).
    + apply CRealEq_sym. apply CReal_plus_opp_r.
    + apply CReal_plus_proper_r. apply CRealEq_sym. apply H.
Qed.

Lemma CReal_isRing : ring_theory (inject_Q 0) (inject_Q 1)
                                 CReal_plus CReal_mult
                                 CReal_minus CReal_opp
                                 CRealEq.
Proof.
  intros. split.
  - apply CReal_plus_0_l.
  - apply CReal_plus_comm.
  - intros x y z. symmetry. apply CReal_plus_assoc.
  - apply CReal_mult_1_l.
  - apply CReal_mult_comm.
  - intros x y z. symmetry. apply CReal_mult_assoc.
  - intros x y z. rewrite <- (CReal_mult_comm z).
    rewrite CReal_mult_plus_distr_l.
    apply (CRealEq_trans _ (CReal_plus (CReal_mult x z) (CReal_mult z y))).
    + apply CReal_plus_proper_r. apply CReal_mult_comm.
    + apply CReal_plus_proper_l. apply CReal_mult_comm.
  - intros x y. apply CRealEq_refl.
  - apply CReal_plus_opp_r.
Qed.

Add Parametric Morphism : CReal_mult
    with signature CRealEq ==> CRealEq ==> CRealEq
      as CReal_mult_morph.
Proof.
  apply CReal_isRingExt.
Qed.

#[global]
Instance CReal_mult_morph_T
  : CMorphisms.Proper
      (CMorphisms.respectful CRealEq (CMorphisms.respectful CRealEq CRealEq)) CReal_mult.
Proof.
  apply CReal_isRingExt.
Qed.

Add Parametric Morphism : CReal_opp
    with signature CRealEq ==> CRealEq
      as CReal_opp_morph.
Proof.
  apply (Ropp_ext CReal_isRingExt).
Qed.

#[global]
Instance CReal_opp_morph_T
  : CMorphisms.Proper
      (CMorphisms.respectful CRealEq CRealEq) CReal_opp.
Proof.
  apply CReal_isRingExt.
Qed.

Add Parametric Morphism : CReal_minus
    with signature CRealEq ==> CRealEq ==> CRealEq
      as CReal_minus_morph.
Proof.
  intros. unfold CReal_minus. rewrite H,H0. reflexivity.
Qed.

#[global]
Instance CReal_minus_morph_T
  : CMorphisms.Proper
      (CMorphisms.respectful CRealEq (CMorphisms.respectful CRealEq CRealEq)) CReal_minus.
Proof.
  intros x y exy z t ezt. unfold CReal_minus. rewrite exy,ezt. reflexivity.
Qed.

Add Ring CRealRing : CReal_isRing.

(**********)
Lemma CReal_mult_1_r : forall r, r * 1 == r.
Proof.
  intro; ring.
Qed.

Lemma CReal_opp_mult_distr_l
  : forall r1 r2 : CReal, - (r1 * r2) == (- r1) * r2.
Proof.
  intros. ring.
Qed.

Lemma CReal_mult_lt_compat_l : forall x y z : CReal,
    0 < x -> y < z -> x*y < x*z.
Proof.
  intros. apply (CReal_plus_lt_reg_l
                   (CReal_opp (CReal_mult x y))).
  rewrite CReal_plus_comm. pose proof CReal_plus_opp_r.
  unfold CReal_minus in H1. rewrite H1.
  rewrite CReal_mult_comm, CReal_opp_mult_distr_l, CReal_mult_comm.
  rewrite <- CReal_mult_plus_distr_l.
  apply CReal_mult_lt_0_compat.
  - exact H.
  - apply (CReal_plus_lt_reg_l y).
    rewrite CReal_plus_comm, CReal_plus_0_l.
    rewrite <- CReal_plus_assoc, H1, CReal_plus_0_l. exact H0.
Qed.

Lemma CReal_mult_lt_compat_r : forall x y z : CReal,
    0 < x -> y < z -> y*x < z*x.
Proof.
  intros. rewrite <- (CReal_mult_comm x), <- (CReal_mult_comm x).
  apply (CReal_mult_lt_compat_l x); assumption.
Qed.

Lemma CReal_mult_eq_reg_l : forall (r r1 r2 : CReal),
    r # 0
    -> r * r1 == r * r2
    -> r1 == r2.
Proof.
  intros. destruct H; split.
  - intro abs. apply (CReal_mult_lt_compat_l (-r)) in abs.
    + rewrite <- CReal_opp_mult_distr_l, <- CReal_opp_mult_distr_l, H0 in abs.
      exact (CRealLe_refl _ abs).
    + apply (CReal_plus_lt_reg_l r).
      rewrite CReal_plus_opp_r, CReal_plus_comm, CReal_plus_0_l. exact c.
  - intro abs. apply (CReal_mult_lt_compat_l (-r)) in abs.
    + rewrite <- CReal_opp_mult_distr_l, <- CReal_opp_mult_distr_l, H0 in abs.
      exact (CRealLe_refl _ abs).
    + apply (CReal_plus_lt_reg_l r).
      rewrite CReal_plus_opp_r, CReal_plus_comm, CReal_plus_0_l. exact c.
  - intro abs. apply (CReal_mult_lt_compat_l r) in abs.
    + rewrite H0 in abs.
      exact (CRealLe_refl _ abs).
    + exact c.
  - intro abs. apply (CReal_mult_lt_compat_l r) in abs.
    + rewrite H0 in abs.
      exact (CRealLe_refl _ abs).
    + exact c.
Qed.

Lemma CReal_abs_appart_zero : forall (x : CReal) (n : Z),
    (2*2^n < Qabs (seq x n))%Q
    -> 0 # x.
Proof.
  intros x n Hapart.
  unfold CReal_appart.
  destruct (Qlt_le_dec 0 (seq x n)).
  - left; exists n; cbn.
    rewrite Qabs_pos in Hapart; lra.
  - right; exists n; cbn.
    rewrite Qabs_neg in Hapart; lra.
Qed.

(*********************************************************)
(** * Field                                              *)
(*********************************************************)

Lemma CRealArchimedean
  : forall x:CReal, { n:Z  &  x < inject_Z n < x+2 }.
Proof.
  intros x.
  (* We add 3/2: 1/2 for the average rounding of floor + 1 to center in the interval.
     This gives a margin of 1/2 in each inequality.
     Since we need margin for Qlt of 2*2^-n plus 2^-n for the real addition, we need n=-3 *)
  remember (seq x (-3)%Z + (3#2))%Q as q eqn: Heqq.
  pose proof (Qlt_floor q) as Hltfloor; unfold QArith_base.inject_Z in Hltfloor.
  pose proof (Qfloor_le q) as Hfloorle; unfold QArith_base.inject_Z in Hfloorle.
  exists (Qfloor q); split.
  - unfold inject_Z, inject_Q, CRealLt. rewrite CReal_red_seq.
    exists (-3)%Z.
    setoid_replace (2 * 2 ^ (-3))%Q with (1#4)%Q by reflexivity.
    subst q; rewrite <- Qinv_plus_distr in Hltfloor.
    lra.
  - unfold inject_Z, inject_Q, CReal_plus, CReal_plus_seq, CRealLt. do 3 rewrite CReal_red_seq.
    exists (-3)%Z.
    setoid_replace (2 * 2 ^ (-3))%Q with (1#4)%Q by reflexivity.
    simplify_seq_idx; rewrite Qred_correct.
    pose proof cauchy x (-3)%Z (-3)%Z (-4)%Z ltac:(lia) ltac:(lia) as Hbnddx.
    rewrite Qabs_Qlt_condition in Hbnddx.
    setoid_replace (2 ^ (-3))%Q with (1#8)%Q in Hbnddx by reflexivity.
    subst q; rewrite <- Qinv_plus_distr in Hltfloor.
    lra.
Qed.

(* ToDo: This is not efficient.
   We take the n for the 2^n lower bound fro x>0.
   This limit can be arbitrarily small and far away from beeing tight.
   To make this really computational, we need to compute a tight
   limit starting from scale x and going down in steps of say 16 bits,
   something which is still easy to compute but likely to succeed. *)

Definition CRealLowerBound (x : CReal) (xPos : 0<x) : Z :=
  proj1_sig (xPos).

Lemma CRealLowerBoundSpec: forall (x : CReal) (xPos : 0<x),
    forall p : Z, (p <= (CRealLowerBound x xPos))%Z
 -> (seq x p > 2^(CRealLowerBound x xPos))%Q.
Proof.
  intros x xPos p Hp.
  unfold CRealLowerBound in *.
  destruct xPos as [n Hn]; unfold proj1_sig in *.
  unfold inject_Q in Hn; rewrite CReal_red_seq in Hn.
  ring_simplify in Hn.
  pose proof cauchy x n n p ltac:(lia) ltac:(lia) as Hxbnd.
  rewrite Qabs_Qlt_condition in Hxbnd.
  lra.
Qed.

Lemma CRealLowerBound_lt_scale: forall (r : CReal) (Hrpos : 0 < r),
    (CRealLowerBound r Hrpos < scale r)%Z.
Proof.
  intros r Hrpos.
  pose proof CRealLowerBoundSpec r Hrpos (CRealLowerBound r Hrpos) ltac:(lia) as Hlow.
  pose proof bound r (CRealLowerBound r Hrpos) as Hup; unfold QBound in Hup.
  apply Qabs_Qlt_condition in Hup. destruct Hup as [_ Hup].
  pose proof Qlt_trans _ _ _ Hlow Hup as Hpow.
  apply Qpower_lt_compat_l_inv in Hpow.
    2: lra.
  exact Hpow.
Qed.

(**
Note on the convergence modulus for x when computing 1/x:
Thinking in terms of absolute and relative errors and scales we get:
- 2^n is absolute error of 1/x (the requested error)
- 2^k is a lower bound of x -> 2^-k is an upper bound of 1/x
For simplicity lets’ say 2^k is the scale of x and 2^-k is the scale of 1/x.

With this we get:
- relative error of 1/x = absolute error of 1/x / scale of 1/x = 2^n / 2^-k = 2^(n+k)
- 1/x maintains relative error
- relative error of x = relative error 1/x = 2^(n+k)
- absolute error of x = relative error x * scale of x = 2^(n+k) * 2^k
- absolute error of x = 2^(n+2*k)
*)

Definition CReal_inv_pos_cm (x : CReal) (xPos : 0 < x) (n : Z):=
  (Z.min (CRealLowerBound x xPos) (n + 2 * (CRealLowerBound x xPos)))%Z.

Definition CReal_inv_pos_seq (x : CReal) (xPos : 0 < x) (n : Z) :=
  (/ seq x (CReal_inv_pos_cm x xPos n))%Q.

Definition CReal_inv_pos_scale (x : CReal) (xPos : 0 < x) : Z :=
  (- (CRealLowerBound x xPos))%Z.

Lemma CReal_inv_pos_cauchy: forall (x : CReal) (xPos : 0 < x),
    QCauchySeq (CReal_inv_pos_seq x xPos).
Proof.
  intros x Hxpos n p q Hp Hq; unfold CReal_inv_pos_seq.
  unfold CReal_inv_pos_cm; remember (CRealLowerBound x Hxpos) as k.

  (* These auxilliary lemmas are required a few times below *)
  assert (forall m:Z, (2^k < seq x (Z.min k (m + 2 * k))))%Q as AuxAppart.
  {
    intros m.
    pose proof CRealLowerBoundSpec x Hxpos (Z.min k (m + 2 * k))%Z ltac:(lia) as H1.
    rewrite Heqk at 1.
    lra.
  }
  assert (forall m:Z, (0 < seq x (Z.min k (m + 2 * k))))%Q as AuxPos.
  {
    intros m.
    pose proof AuxAppart m as H1.
    pose proof Qpower_0_lt 2 k as H2.
    lra.
  }

  assert( forall a b : Q, (a>0)%Q -> (b>0)%Q -> (/a - /b == (b - a) / (a * b))%Q )
  as H by (intros; field; lra); rewrite H by apply AuxPos; clear H.

  setoid_rewrite Qabs_Qmult; setoid_rewrite Qabs_Qinv.
  apply Qlt_shift_div_r.
  - setoid_rewrite <- (Qmult_0_l 0); setoid_rewrite Qabs_Qmult.
    apply Qmult_lt_compat_nonneg.
    1,2: split; [lra | apply Qabs_gt, AuxPos].
  - assert( forall r:Q, (r == (r/2^k/2^k)*(2^k*2^k))%Q )
      as H by (intros r; field; apply Qpower_not_0; lra); rewrite H; clear H.
    apply Qmult_lt_compat_nonneg.
    + split.
      * do 2 (apply Qle_shift_div_l; [ apply Qpower_0_lt; lra | rewrite Qmult_0_l ]).
        apply Qabs_nonneg.
      * do 2 (apply Qlt_shift_div_r; [apply Qpower_0_lt; lra|]).
        do 2 rewrite <- Qpower_plus by lra.
        apply (cauchy x (n+k+k)%Z); lia.
    + split.
      * rewrite <- Qpower_plus by lra.
        apply Qpower_pos; lra.
      * setoid_rewrite Qabs_Qmult; apply Qmult_lt_compat_nonneg.
        1,2: split; [apply Qpower_pos; lra | ].
        1,2: apply Qabs_gt, AuxAppart.
Qed.

Lemma CReal_inv_pos_bound : forall (x : CReal) (Hxpos : 0 < x),
  QBound (CReal_inv_pos_seq x Hxpos) (CReal_inv_pos_scale x Hxpos).
Proof.
  intros x Hxpos n.
  unfold CReal_inv_pos_seq, CReal_inv_pos_scale, CReal_inv_pos_cm.
  remember (CRealLowerBound x Hxpos) as k.
  pose proof CRealLowerBoundSpec x Hxpos (Z.min k (n + 2 * k))%Z ltac:(lia) as Hlb.
  rewrite <- Heqk in Hlb.
  rewrite Qabs_pos.
    2: apply Qinv_le_0_compat; pose proof Qpower_pos 2 k; lra.
  rewrite Qpower_opp; apply -> Qinv_lt_contravar.
  - exact Hlb.
  - pose proof Qpower_0_lt 2 k; lra.
  - apply Qpower_0_lt; lra.
Qed.

Definition CReal_inv_pos (x : CReal) (Hxpos : 0 < x) : CReal :=
{|
  seq := CReal_inv_pos_seq x Hxpos;
  scale := CReal_inv_pos_scale x Hxpos;
  cauchy := CReal_inv_pos_cauchy x Hxpos;
  bound := CReal_inv_pos_bound x Hxpos
|}.

Definition CReal_neg_lt_pos : forall x : CReal, x < 0 -> 0 < -x.
Proof.
  intros x [n nmaj]. exists n.
  simpl in *. unfold CReal_opp_seq, Qminus.
  abstract now rewrite Qplus_0_r, <- (Qplus_0_l (- seq x n)).
Defined.

Definition CReal_inv (x : CReal) (xnz : x # 0) : CReal
  := match xnz with
     | inl xNeg => - CReal_inv_pos (-x) (CReal_neg_lt_pos x xNeg)
     | inr xPos => CReal_inv_pos x xPos
     end.

Notation "/ x" := (CReal_inv x) (at level 35, right associativity) : CReal_scope.

Lemma CReal_inv_0_lt_compat
  : forall (r : CReal) (rnz : r # 0),
    0 < r -> 0 < ((/ r) rnz).
Proof.
  intros r Hrnz Hrpos; unfold CReal_inv; cbn.
  destruct Hrnz.
  - exfalso. apply CRealLt_asym in Hrpos. contradiction.
  - unfold CRealLt.
    exists (- (scale r) - 1)%Z.
    unfold inject_Q; rewrite CReal_red_seq; simplify_Qlt.
    unfold CReal_inv_pos; rewrite CReal_red_seq.
    unfold CReal_inv_pos_seq.
    pose proof bound r as Hrbnd; unfold QBound in Hrbnd.
    rewrite Qpower_minus by lra.
    field_simplify (2 * (2 ^ (- scale r) / 2 ^ 1))%Q.
    rewrite Qpower_opp; apply -> Qinv_lt_contravar.
    + setoid_rewrite Qabs_Qlt_condition in Hrbnd.
      specialize (Hrbnd (CReal_inv_pos_cm r c (- scale r - 1))%Z).
      lra.
    + apply Qpower_0_lt; lra.
    + unfold CReal_inv_pos_cm.
      pose proof CRealLowerBoundSpec r c
        ((Z.min (CRealLowerBound r c) (- scale r - 1 + 2 * CRealLowerBound r c)))%Z ltac:(lia) as Hlowbnd.
      pose proof Qpower_0_lt 2 (CRealLowerBound r c) as Hpow.
      lra.
Qed.

Lemma CReal_inv_l_pos : forall (r:CReal) (Hrpos : 0 < r),
    (CReal_inv_pos r Hrpos) * r == 1.
Proof.
  intros r Hrpos; apply CRealEq_diff; intros n.
  unfold CReal_mult, CReal_mult_seq, CReal_mult_scale;
  unfold CReal_inv_pos, CReal_inv_pos_seq, CReal_inv_pos_scale, CReal_inv_pos_cm;
  unfold inject_Q.
  do 3 rewrite CReal_red_seq.
  do 1 rewrite CReal_red_scale.
  simplify_seq_idx.

  (* This is needed several times below *)
  remember (Z.min (CRealLowerBound r Hrpos) (n - scale r - 1 + 2 * CRealLowerBound r Hrpos))%Z as k.
  assert (0 < seq r k)%Q as Hrseqpos.
  { pose proof Qpower_0_lt 2 (CRealLowerBound r Hrpos)%Z ltac:(lra) as Hpow.
    pose proof CRealLowerBoundSpec r Hrpos k ltac:(lia) as Hlowbnd.
    lra.
  }
  field_simplify_Qabs; [|lra]; unfold Qdiv.
  rewrite Qabs_Qmult, Qabs_Qinv.
  apply Qle_shift_div_r.
    1: apply Qabs_gt; lra.

  pose proof cauchy r (n + CRealLowerBound r Hrpos)%Z
    (n + CRealLowerBound r Hrpos - 1)%Z k as Hrbnd.
  pose proof CRealLowerBound_lt_scale r Hrpos as Hscale_lowbnd.
  specialize (Hrbnd ltac:(lia) ltac:(lia)).
  simplify_Qabs_in Hrbnd; simplify_Qabs.
  rewrite Qplus_comm in Hrbnd.
  apply Qlt_le_weak in Hrbnd.
  apply (Qle_trans _ _ _ Hrbnd).

  pose proof CRealLowerBoundSpec r Hrpos k ltac:(lia) as Hlowbnd.

  rewrite Qpower_plus; [|lra].
  apply Qmult_le_compat_nonneg.
  { pose proof Qpower_pos 2 n; split; lra. }
  split.
  - apply Qpower_pos; lra.
  - rewrite Qabs_pos; [lra|].
    pose proof Qpower_0_lt 2 (CRealLowerBound r Hrpos)%Z ltac:(lra) as Hpow.
    lra.
Qed.

Lemma CReal_inv_l : forall (r:CReal) (rnz : r # 0),
        ((/ r) rnz) * r == 1.
Proof.
  intros. unfold CReal_inv. destruct rnz.
  - rewrite <- CReal_opp_mult_distr_l, CReal_opp_mult_distr_r.
    apply CReal_inv_l_pos.
  - apply CReal_inv_l_pos.
Qed.

Lemma CReal_inv_r : forall (r:CReal) (rnz : r # 0),
    r * ((/ r) rnz) == 1.
Proof.
  intros. rewrite CReal_mult_comm, CReal_inv_l.
  reflexivity.
Qed.

Lemma CReal_inv_1 : forall nz : 1 # 0, (/ 1) nz == 1.
Proof.
  intros. rewrite <- (CReal_mult_1_l ((/1) nz)). rewrite CReal_inv_r.
  reflexivity.
Qed.

Lemma CReal_inv_mult_distr :
  forall r1 r2 (r1nz : r1 # 0) (r2nz : r2 # 0) (rmnz : (r1*r2) # 0),
    (/ (r1 * r2)) rmnz == (/ r1) r1nz * (/ r2) r2nz.
Proof.
  intros. apply (CReal_mult_eq_reg_l r1).
  - exact r1nz.
  - rewrite <- CReal_mult_assoc. rewrite CReal_inv_r. rewrite CReal_mult_1_l.
    apply (CReal_mult_eq_reg_l r2).
    + exact r2nz.
    + rewrite CReal_inv_r. rewrite <- CReal_mult_assoc.
      rewrite (CReal_mult_comm r2 r1). rewrite CReal_inv_r.
      reflexivity.
Qed.

Lemma Rinv_eq_compat : forall x y (rxnz : x # 0) (rynz : y # 0),
    x == y
    -> (/ x) rxnz == (/ y) rynz.
Proof.
  intros. apply (CReal_mult_eq_reg_l x).
  - exact rxnz.
  - rewrite CReal_inv_r, H, CReal_inv_r. reflexivity.
Qed.

Lemma CReal_mult_lt_reg_l : forall r r1 r2, 0 < r -> r * r1 < r * r2 -> r1 < r2.
Proof.
  intros z x y H H0.
  apply (CReal_mult_lt_compat_l ((/z) (inr H))) in H0.
  - repeat rewrite <- CReal_mult_assoc in H0. rewrite CReal_inv_l in H0.
    repeat rewrite CReal_mult_1_l in H0. apply H0.
  - apply CReal_inv_0_lt_compat. exact H.
Qed.

Lemma CReal_mult_lt_reg_r : forall r r1 r2, 0 < r -> r1 * r < r2 * r -> r1 < r2.
Proof.
  intros.
  apply CReal_mult_lt_reg_l with r.
  - exact H.
  - now rewrite 2!(CReal_mult_comm r).
Qed.

Lemma CReal_mult_eq_reg_r : forall r r1 r2, r1 * r == r2 * r -> r # 0 -> r1 == r2.
Proof.
  intros. apply (CReal_mult_eq_reg_l r).
  - exact H0.
  - now rewrite 2!(CReal_mult_comm r).
Qed.

Lemma CReal_mult_eq_compat_l : forall r r1 r2, r1 == r2 -> r * r1 == r * r2.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma CReal_mult_eq_compat_r : forall r r1 r2, r1 == r2 -> r1 * r == r2 * r.
Proof.
  intros. rewrite H. reflexivity.
Qed.

(* In particular x * y == 1 implies that 0 # x, 0 # y and
   that x and y are inverses of each other. *)
Lemma CReal_mult_pos_appart_zero : forall x y : CReal, 0 < x * y -> 0 # x.
Proof.
  intros x y H0ltxy.
  unfold CRealLt, CReal_mult, CReal_mult_seq, CReal_mult_scale in H0ltxy;
    rewrite CReal_red_seq in H0ltxy.
  destruct H0ltxy as [n nmaj].
  cbn in nmaj; setoid_rewrite Qplus_0_r in nmaj.
  destruct (Q_dec 0 (seq y (n - scale x - 1)))%Q as [[H0lty|Hylt0]|Hyeq0].
  - apply (Qmult_lt_compat_r _ _ (/(seq y (n - scale x - 1)))%Q ) in nmaj.
      2: apply Qinv_lt_0_compat, H0lty.
    setoid_rewrite <- Qmult_assoc in nmaj at 2.
    setoid_rewrite Qmult_inv_r in nmaj.
      2: lra.
    setoid_rewrite Qmult_1_r in nmaj.
    pose proof bound y (n - scale x - 1)%Z as Hybnd.
    apply Qabs_Qlt_condition, proj2 in Hybnd.
    apply Qinv_lt_contravar in Hybnd.
      3: apply Qpower_0_lt; lra.
      2: exact H0lty.
    apply (Qmult_lt_l _ _ (2 * (2 ^ n))) in Hybnd.
      2: pose proof Qpower_0_lt 2 n; lra.
    apply (Qlt_trans _ _ _ Hybnd) in nmaj; clear Hybnd.
    rewrite <- Qpower_opp, <- Qmult_assoc, <- Qpower_plus in nmaj by lra.
    apply (CReal_abs_appart_zero x (n - scale y - 1)%Z), Qabs_gt.
    rewrite Qpower_minus_pos.
    ring_simplify. ring_simplify (n + - scale y)%Z in nmaj.
    pose proof Qpower_0_lt 2 (n - scale y)%Z; lra.
  - (* This proof is the same as above, except that we swap the signs of x and y *)
    (* ToDo: maybe assert teh goal for arbitrary y>0 and then apply twice *)
    assert (forall a b : Q, ((-a)*(-b)==a*b)%Q) by (intros; ring).
    setoid_rewrite <- H in nmaj at 2; clear H.
    apply (Qmult_lt_compat_r _ _ (/-(seq y (n - scale x - 1)))%Q ) in nmaj.
      2: apply Qinv_lt_0_compat; lra.
    setoid_rewrite <- Qmult_assoc in nmaj at 2.
    setoid_rewrite Qmult_inv_r in nmaj.
      2: lra.
    setoid_rewrite Qmult_1_r in nmaj.
    pose proof bound y (n - scale x - 1)%Z as Hybnd.
    apply Qabs_Qlt_condition, proj1 in Hybnd.
    apply Qopp_lt_compat in Hybnd; rewrite Qopp_involutive in Hybnd.
    apply Qinv_lt_contravar in Hybnd.
      3: apply Qpower_0_lt; lra.
      2: lra.
    apply (Qmult_lt_l _ _ (2 * (2 ^ n))) in Hybnd.
      2: pose proof Qpower_0_lt 2 n; lra.
    apply (Qlt_trans _ _ _ Hybnd) in nmaj; clear Hybnd.
    rewrite <- Qpower_opp, <- Qmult_assoc, <- Qpower_plus in nmaj by lra.
    apply (CReal_abs_appart_zero x (n - scale y - 1)%Z).
    pose proof Qpower_0_lt 2 (n + - scale y)%Z ltac:(lra) as Hpowpos.
    rewrite Qabs_neg by lra.
    rewrite Qpower_minus_pos.
    ring_simplify. ring_simplify (n + - scale y)%Z in nmaj.
    pose proof Qpower_0_lt 2 (n - scale y)%Z; lra.
  - pose proof Qpower_0_lt 2 n ltac:(lra).
    rewrite <- Hyeq0 in nmaj. lra.
Qed.

Fixpoint pow (r:CReal) (n:nat) : CReal :=
  match n with
    | O => 1
    | S n => r * (pow r n)
  end.


Lemma CReal_mult_le_compat_l_half : forall r r1 r2,
    0 < r -> r1 <= r2 -> r * r1 <= r * r2.
Proof.
  intros. intro abs. apply (CReal_mult_lt_reg_l) in abs.
  - contradiction.
  - apply H.
Qed.

Lemma CReal_invQ : forall (b : positive) (pos : Qlt 0 (Z.pos b # 1)),
    CReal_inv (inject_Q (Z.pos b # 1)) (inr (CReal_injectQPos (Z.pos b # 1) pos))
    == inject_Q (1 # b).
Proof.
  intros.
  apply (CReal_mult_eq_reg_l (inject_Q (Z.pos b # 1))).
  - right. apply CReal_injectQPos. exact pos.
  - rewrite CReal_mult_comm, CReal_inv_l.
    apply CRealEq_diff. intro n. simpl.
    do 2 rewrite Pos.mul_1_r. rewrite Z.pos_sub_diag.
    pose proof Qpower_pos 2 n ltac:(lra). rewrite Z.abs_0, Qreduce_zero. lra.
Qed.

Definition CRealQ_dense (a b : CReal)
  : a < b -> { q : Q  &  a < inject_Q q < b }.
Proof.
  (* Locate a and b at the index given by a<b,
     and pick the middle rational number. *)
  intros [p pmaj].
  exists ((seq a p + seq b p) * (1#2))%Q.
  split.
  - apply (CReal_le_lt_trans _ _ _ (inject_Q_compare a p)). apply inject_Q_lt.
    lra.
  - apply (CReal_plus_lt_reg_l (-b)).
    rewrite CReal_plus_opp_l.
    apply (CReal_plus_lt_reg_r
             (-inject_Q ((seq a p + seq b p) * (1 # 2)))).
    rewrite CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_r, CReal_plus_0_l.
    rewrite <- opp_inject_Q.
    apply (CReal_le_lt_trans _ _ _ (inject_Q_compare (-b) p)). apply inject_Q_lt.
    destruct b as [bseq]; simpl in pmaj |- *.
    unfold CReal_opp_seq; rewrite CReal_red_seq.
    lra.
Qed.

Lemma inject_Q_mult : forall q r : Q,
    inject_Q (q * r) == inject_Q q * inject_Q r.
Proof.
  split.
  - intros [n maj]; cbn in maj.
    unfold CReal_mult_seq in maj; cbn in maj.
    pose proof Qpower_0_lt 2 n; lra.
  - intros [n maj]; cbn in maj.
    unfold CReal_mult_seq in maj; cbn in maj.
    pose proof Qpower_0_lt 2 n; lra.
Qed.

Definition Rup_nat (x : CReal)
  : { n : nat & x < inject_Q (Z.of_nat n #1) }.
Proof.
  intros. destruct (CRealArchimedean x) as [p maj].
  destruct p.
  - exists O. apply maj.
  - exists (Pos.to_nat p). rewrite positive_nat_Z. apply maj.
  - exists O. apply (CReal_lt_trans _ (inject_Q (Z.neg p # 1))).
    + apply maj.
    + apply inject_Q_lt. reflexivity.
Qed.

Lemma CReal_mult_le_0_compat : forall (a b : CReal),
    0 <= a -> 0 <= b -> 0 <= a * b.
Proof.
  (* Limit of (a + 1/n)*b when n -> infty. *)
  intros. intro abs.
  assert (0 < -(a*b)) as epsPos.
  { rewrite <- CReal_opp_0. apply CReal_opp_gt_lt_contravar. exact abs. }
  destruct (Rup_nat (b * (/ (-(a*b))) (inr epsPos)))
    as [n maj].
  destruct n as [|n].
  - apply (CReal_mult_lt_compat_r (-(a*b))) in maj.
    + rewrite CReal_mult_0_l, CReal_mult_assoc, CReal_inv_l, CReal_mult_1_r in maj.
      contradiction.
    + exact epsPos.
  - (* n > 0 *)
    assert (0 < inject_Q (Z.of_nat (S n) #1)) as nPos.
    { apply inject_Q_lt. unfold Qlt, Qnum, Qden.
      do 2 rewrite Z.mul_1_r. apply Z2Nat.inj_lt.
      - discriminate.
      - apply Zle_0_nat.
      - rewrite Nat2Z.id. apply -> Nat.succ_le_mono; apply Nat.le_0_l. }
    assert (b * (/ inject_Q (Z.of_nat (S n) #1)) (inr nPos) < -(a*b)).
    { apply (CReal_mult_lt_reg_r (inject_Q (Z.of_nat (S n) #1))). { apply nPos. }
      rewrite CReal_mult_assoc, CReal_inv_l, CReal_mult_1_r.
      apply (CReal_mult_lt_compat_r (-(a*b))) in maj.
      - rewrite CReal_mult_assoc, CReal_inv_l, CReal_mult_1_r in maj.
        rewrite CReal_mult_comm. apply maj.
      - apply epsPos. }
    pose proof (CReal_mult_le_compat_l_half
                  (a + (/ inject_Q (Z.of_nat (S n) #1)) (inr nPos)) 0 b).
    assert (0 + 0 < a + (/ inject_Q (Z.of_nat (S n) #1)) (inr nPos)).
    { apply CReal_plus_le_lt_compat. { apply H. } apply CReal_inv_0_lt_compat. apply nPos. }
    rewrite CReal_plus_0_l in H3. specialize (H2 H3 H0).
    clear H3. rewrite CReal_mult_0_r in H2.
    apply H2. clear H2. rewrite CReal_mult_plus_distr_r.
    apply (CReal_plus_lt_compat_l (a*b)) in H1.
    rewrite CReal_plus_opp_r in H1.
    rewrite (CReal_mult_comm ((/ inject_Q (Z.of_nat (S n) #1)) (inr nPos))).
    apply H1.
Qed.

Lemma CReal_mult_le_compat_l : forall (r r1 r2:CReal),
    0 <= r -> r1 <= r2 -> r * r1 <= r * r2.
Proof.
  intros. apply (CReal_plus_le_reg_r (-(r*r1))).
  rewrite CReal_plus_opp_r, CReal_opp_mult_distr_r.
  rewrite <- CReal_mult_plus_distr_l.
  apply CReal_mult_le_0_compat. { exact H. }
  apply (CReal_plus_le_reg_r r1).
  rewrite CReal_plus_0_l, CReal_plus_assoc, CReal_plus_opp_l, CReal_plus_0_r.
  exact H0.
Qed.

Lemma CReal_mult_le_compat_r : forall (r r1 r2:CReal),
    0 <= r -> r1 <= r2 -> r1 * r <= r2 * r.
Proof.
  intros. apply (CReal_plus_le_reg_r (-(r1*r))).
  rewrite CReal_plus_opp_r, CReal_opp_mult_distr_l.
  rewrite <- CReal_mult_plus_distr_r.
  apply CReal_mult_le_0_compat. 2: exact H.
  apply (CReal_plus_le_reg_r r1). ring_simplify. exact H0.
Qed.

Lemma CReal_mult_le_reg_l :
  forall x y z : CReal,
    0 < x -> x * y <= x * z -> y <= z.
Proof.
  intros. intro abs.
  apply (CReal_mult_lt_compat_l x) in abs.
  - contradiction.
  - exact H.
Qed.

Lemma CReal_mult_le_reg_r :
  forall x y z : CReal,
    0 < x -> y * x <= z * x -> y <= z.
Proof.
  intros. intro abs.
  apply (CReal_mult_lt_compat_r x) in abs.
  - contradiction.
  - exact H.
Qed.
