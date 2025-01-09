Require Import QArith.
Require Import Qpower.
Require Import Qabs.
Require Import Qround.
Require Import Zorder.
Require Import Lia.
Require Import Lqa. (* This is only used in a few places and could be avoided *)
Require Import PosExtra.

(** * Power of 2 open and closed upper and lower bounds for [q : Q] *)

Fixpoint Pos_log2floor_plus1 (p : positive) : positive :=
  match p with
  | (p'~1)%positive => Pos.succ (Pos_log2floor_plus1 p')
  | (p'~0)%positive => Pos.succ (Pos_log2floor_plus1 p')
  | 1%positive      => 1
  end.

Lemma Pos_log2floor_plus1_spec : forall (p : positive),
  (Pos.pow 2 (Pos_log2floor_plus1 p) <= 2 * p < 2 * Pos.pow 2 (Pos_log2floor_plus1 p))%positive.
Proof.
  intros p.
  split.
  - induction p.
    + cbn. rewrite Pos.pow_succ_r. lia.
    + cbn. rewrite Pos.pow_succ_r. lia.
    + cbn. lia.
  - induction p.
    + cbn. rewrite Pos.pow_succ_r. lia.
    + cbn. rewrite Pos.pow_succ_r. lia.
    + cbn. lia.
Qed.

Fixpoint Pos_log2ceil_plus1 (p : positive) : positive :=
  match p with
  | (p'~1)%positive => Pos.succ (Pos.succ (Pos_log2floor_plus1 p'))
  | (p'~0)%positive => Pos.succ (Pos_log2ceil_plus1 p')
  | 1%positive      => 1
  end.

Lemma Pos_log2ceil_plus1_spec : forall (p : positive),
  (Pos.pow 2 (Pos_log2ceil_plus1 p) < 4 * p <= 2 * Pos.pow 2 (Pos_log2ceil_plus1 p))%positive.
Proof.
  intros p.
  split.
  - induction p.
    + cbn. do 2 rewrite Pos.pow_succ_r.
      pose proof Pos_log2floor_plus1_spec p. lia.
    + cbn. rewrite Pos.pow_succ_r. lia.
    + cbn. lia.
  - induction p.
    + cbn. do 2 rewrite Pos.pow_succ_r.
      pose proof Pos_log2floor_plus1_spec p. lia.
    + cbn. rewrite Pos.pow_succ_r. lia.
    + cbn. lia.
Qed.

Fixpoint Pos_is_pow2 (p : positive) : bool :=
  match p with
  | (p'~1)%positive => false
  | (p'~0)%positive => Pos_is_pow2 p'
  | 1%positive      => true
  end.

(** ** Power of two closed upper bound [q <= 2^z] *)

Definition Qbound_le_ZExp2 (q : Q) : Z :=
  match Qnum q with
  (* The -1000 is a compromise between a tight Archimedian and avoiding too large numbers *)
  | Z0 => -1000
  | Zneg p => 0
  | Zpos p => (Z.pos (Pos_log2ceil_plus1 p) - Z.pos (Pos_log2floor_plus1 (Qden q)))%Z
  end.

Lemma Qbound_le_ZExp2_spec : forall (q : Q),
  (q <= 2^(Qbound_le_ZExp2 q))%Q.
Proof.
  intros q.
  destruct q as [num den]; unfold Qbound_le_ZExp2, Qnum; destruct num.
  - intros contra; inversion contra.
  - rewrite Qpower_minus by lra.
    apply Qle_shift_div_l.
    + apply Qpower_0_lt; lra.
    + do 2 rewrite Qpower_decomp_pos, Pos_pow_1_r.
      unfold Qle, Qmult, Qnum, Qden.
      rewrite Pos.mul_1_r, Z.mul_1_r.
      pose proof Pos_log2ceil_plus1_spec p as Hnom.
      pose proof Pos_log2floor_plus1_spec den as Hden.

      apply (Zorder.Zmult_le_reg_r _ _ 2).
      * lia.
      * replace (Z.pos p * 2 ^ Z.pos (Pos_log2floor_plus1 den) * 2)%Z
          with ((Z.pos p * 2) * 2 ^ Z.pos (Pos_log2floor_plus1 den))%Z by ring.
        replace (2 ^ Z.pos (Pos_log2ceil_plus1 p) * Z.pos den * 2)%Z
          with (2 ^ Z.pos (Pos_log2ceil_plus1 p) * (Z.pos den * 2))%Z by ring.
        apply Z.mul_le_mono_nonneg; lia.
  - intros contra; inversion contra.
Qed.

Definition Qbound_leabs_ZExp2 (q : Q) : Z := Qbound_le_ZExp2 (Qabs q).

Lemma Qbound_leabs_ZExp2_spec : forall (q : Q),
  (Qabs q <= 2^(Qbound_leabs_ZExp2 q))%Q.
Proof.
  intros q.
  unfold Qbound_leabs_ZExp2; apply Qabs_case; intros.
  1,2: apply Qbound_le_ZExp2_spec.
Qed.

(** ** Power of two open upper bound [q < 2^z] and [Qabs q < 2^z] *)

(** Compute a z such that q<2^z.
    z shall be close to as small as possible, but we need a compromise between
    the tighness of the bound and the computation speed and proof complexity.
    Looking just at the log2 of the numerator and denominator, this is a tight bound
    except when the numerator is a power of 2 and the denomintor is not.
    E.g. this return 4/5 < 2^1 instead of 4/5< 2^0.
    If q==0, we return -1000, because as binary integer this has just 10 bits but
    2^-1000 should be smaller than almost any number in practice.
    If numbers are much smaller, computations might be inefficient. *)

Definition Qbound_lt_ZExp2 (q : Q) : Z :=
  match Qnum q with
  (* The -1000 is a compromise between a tight Archimedian and avoiding too large numbers *)
  | Z0 => -1000
  | Zneg p => 0
  | Zpos p => Z.pos_sub (Pos.succ (Pos_log2floor_plus1 p)) (Pos_log2floor_plus1 (Qden q))
  end.

Remark Qbound_lt_ZExp2_test_1 : Qbound_lt_ZExp2 (4#4) = 1%Z. reflexivity. Qed.
Remark Qbound_lt_ZExp2_test_2 : Qbound_lt_ZExp2 (5#4) = 1%Z. reflexivity. Qed.
Remark Qbound_lt_ZExp2_test_3 : Qbound_lt_ZExp2 (4#5) = 1%Z. reflexivity. Qed.
Remark Qbound_lt_ZExp2_test_4 : Qbound_lt_ZExp2 (7#5) = 1%Z. reflexivity. Qed.

Lemma Qbound_lt_ZExp2_spec : forall (q : Q),
  (q < 2^(Qbound_lt_ZExp2 q))%Q.
Proof.
  intros q.
  destruct q as [num den]; unfold Qbound_lt_ZExp2, Qnum; destruct num.
  - reflexivity.
  - (* Todo: A lemma like Pos2Z.add_neg_pos for minus would be nice *)
    change
      (Z.pos_sub (Pos.succ (Pos_log2floor_plus1 p)) (Pos_log2floor_plus1 (Qden (Z.pos p # den))))%Z
      with
      ((Z.pos (Pos.succ (Pos_log2floor_plus1 p)) - Z.pos (Pos_log2floor_plus1 (Qden (Z.pos p # den)))))%Z.
    rewrite Qpower_minus by lra.
    apply Qlt_shift_div_l.
    + apply Qpower_0_lt; lra.
    + do 2 rewrite Qpower_decomp_pos, Pos_pow_1_r.
      unfold Qlt, Qmult, Qnum, Qden.
      rewrite Pos.mul_1_r, Z.mul_1_r.
      pose proof Pos_log2floor_plus1_spec p as Hnom.
      pose proof Pos_log2floor_plus1_spec den as Hden.
      apply (Zmult_lt_reg_r _ _ 2).
      * lia.
      * rewrite Pos2Z.inj_succ, <- Z.add_1_r.
        rewrite Z.pow_add_r by lia.

        replace (Z.pos p * 2 ^ Z.pos (Pos_log2floor_plus1 den) * 2)%Z
          with (2 ^ Z.pos (Pos_log2floor_plus1 den) * (Z.pos p * 2))%Z by ring.
        replace (2 ^ Z.pos (Pos_log2floor_plus1 p) * 2 ^ 1 * Z.pos den * 2)%Z
          with ((Z.pos den * 2) * (2 * 2 ^ Z.pos (Pos_log2floor_plus1 p)))%Z by ring.

        (* ToDo: this is weaker than neccessary: Z.mul_lt_mono_nonneg. *)
        apply Zmult_lt_compat2; lia.
  - cbn.
    (* ToDo: lra could know that negative fractions are negative *)
    assert (Z.neg p # den < 0) as Hnegfrac by (unfold Qlt, Qnum, Qden; lia).
    lra.
Qed.

Definition Qbound_ltabs_ZExp2 (q : Q) : Z := Qbound_lt_ZExp2 (Qabs q).

Lemma Qbound_ltabs_ZExp2_spec : forall (q : Q),
  (Qabs q < 2^(Qbound_ltabs_ZExp2 q))%Q.
Proof.
  intros q.
  unfold Qbound_ltabs_ZExp2; apply Qabs_case; intros.
  1,2: apply Qbound_lt_ZExp2_spec.
Qed.

(** ** Power of 2 open lower bounds for [2^z < q] and [2^z < Qabs q] *)

(** Note: the -2 is required cause of the Qlt limit.
    In case q is a power of two, the lower and upper bound must be a factor of 4 apart *)
Definition Qlowbound_ltabs_ZExp2 (q : Q) : Z := -2 + Qbound_ltabs_ZExp2 q.

Lemma Qlowbound_ltabs_ZExp2_inv: forall q : Q,
    q > 0
 -> Qlowbound_ltabs_ZExp2 q = (- Qbound_ltabs_ZExp2 (/q))%Z.
Proof.
  intros q Hqgt0.
  destruct q as [n d].
  unfold Qlowbound_ltabs_ZExp2, Qbound_ltabs_ZExp2, Qbound_lt_ZExp2, Qnum.
  destruct n.
  - inversion Hqgt0.
  - unfold Qabs, Z.abs, Qinv, Qnum, Qden.
    rewrite -> Z.pos_sub_opp.
    do 2 rewrite <- Pos2Z.add_pos_neg.
    lia.
  - inversion Hqgt0.
Qed.

Lemma Qlowbound_ltabs_ZExp2_opp: forall q : Q,
  (Qlowbound_ltabs_ZExp2 q = Qlowbound_ltabs_ZExp2 (-q))%Z.
Proof.
  intros q.
  destruct q as [[|n|n] d]; reflexivity.
Qed.

Lemma Qlowbound_lt_ZExp2_spec : forall (q : Q) (Hqgt0 : q > 0),
  (2^(Qlowbound_ltabs_ZExp2 q) < q)%Q.
Proof.
  intros q Hqgt0.
  pose proof Qbound_ltabs_ZExp2_spec (/q) as Hspecub.
  rewrite Qlowbound_ltabs_ZExp2_inv by exact Hqgt0.
  rewrite Qpower_opp.
  setoid_rewrite <- (Qinv_involutive q) at 2.
  apply -> Qinv_lt_contravar.
  - rewrite Qabs_pos in Hspecub.
    + exact Hspecub.
    + apply Qlt_le_weak, Qinv_lt_0_compat, Hqgt0.
  - apply Qpower_0_lt; lra.
  - apply Qinv_lt_0_compat, Hqgt0.
Qed.

Lemma Qlowbound_ltabs_ZExp2_spec : forall (q : Q) (Hqgt0 : ~ q == 0),
  (2^(Qlowbound_ltabs_ZExp2 q) < Qabs q)%Q.
Proof.
  intros q Hqgt0.
  destruct (Q_dec 0 q) as [[H|H]|H].
  - rewrite Qabs_pos by lra.
    apply Qlowbound_lt_ZExp2_spec, H.
  - rewrite Qabs_neg by lra.
    rewrite Qlowbound_ltabs_ZExp2_opp.
    apply Qlowbound_lt_ZExp2_spec.
    lra.
  - lra.
Qed.

(** ** Existential formulations of power of 2 lower and upper bounds *)

Definition QarchimedeanExp2_Z (q : Q)
  :  {z : Z | (q < 2^z)%Q}
  := exist _ (Qbound_lt_ZExp2 q) (Qbound_lt_ZExp2_spec q).

Definition QarchimedeanAbsExp2_Z (q : Q)
  :  {z : Z | (Qabs q < 2^z)%Q}
  := exist _ (Qbound_ltabs_ZExp2 q) (Qbound_ltabs_ZExp2_spec q).

Definition QarchimedeanLowExp2_Z (q : Q) (Hqgt0 : q > 0)
  :  {z : Z | (2^z < q)%Q}
  := exist _ (Qlowbound_ltabs_ZExp2 q) (Qlowbound_lt_ZExp2_spec q Hqgt0).

Definition QarchimedeanLowAbsExp2_Z (q : Q) (Hqgt0 : ~ q == 0)
  :  {z : Z | (2^z < Qabs q)%Q}
  := exist _ (Qlowbound_ltabs_ZExp2 q) (Qlowbound_ltabs_ZExp2_spec q Hqgt0).
