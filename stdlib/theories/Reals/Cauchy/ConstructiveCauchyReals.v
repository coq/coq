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

Require Import QArith.
Require Import Qpower.
Require Import Qabs.
Require Import Qround.
Require Import Logic.ConstructiveEpsilon.
Require CMorphisms.
Require Import Lia.
Require Import Lqa.
Require Import QExtra.
Require Import ConstructiveExtra.

(** The constructive Cauchy real numbers, ie the Cauchy sequences
    of rational numbers.

    Cauchy reals are Cauchy sequences of rational numbers,
    equipped with explicit moduli of convergence and
    an equivalence relation (the difference converges to zero).

    Without convergence moduli, we would fail to prove that a Cauchy
    sequence of constructive reals converges.

    Because of the Specker sequences (increasing, computable
    and bounded sequences of rationals that do not converge
    to a computable real number), constructive reals do not
    follow the least upper bound principle.

    The double quantification on p q is needed to avoid
    forall un, QSeqEquiv un (fun _ => un O) (fun q => O)
    which says nothing about the limit of un.

    We define sequences as Z -> Q instead of nat -> Q,
    so that we can compute arguments like 2^n fast.

    Todo: doc for Z->Q

    WARNING: this module is not meant to be imported directly,
    please import `Reals.Abstract.ConstructiveReals` instead.

    WARNING: this file is experimental and likely to change in future releases.
 *)

Definition QCauchySeq (xn : Z -> Q)
  : Prop
  := forall (k : Z) (p q : Z),
      Z.le p k
   -> Z.le q k
   -> Qabs (xn p - xn q) < 2 ^ k.

Definition QBound (xn : Z -> Q) (scale : Z)
  : Prop
  := forall (k : Z),
      Qabs (xn k) < 2 ^ scale.

(* A Cauchy real is a sequence with a proof that the sequence is Cauchy *)
Record CReal := mkCReal {
  seq : Z -> Q;
  scale : Z;
  cauchy : QCauchySeq seq;
  bound : QBound seq scale
}.

Declare Scope CReal_scope.

(* Declare Scope R_scope with Key R *)
Delimit Scope CReal_scope with CReal.

(* Automatically open scope R_scope for arguments of type R *)
Bind Scope CReal_scope with CReal.

Local Open Scope CReal_scope.

Definition CRealLt (x y : CReal) : Set
  := { n : Z |  Qlt (2 * 2 ^ n) (seq y n - seq x n) }.

Definition CRealLtProp (x y : CReal) : Prop
  := exists n : Z, Qlt (2 * 2 ^ n)(seq y n - seq x n).

Definition CRealGt (x y : CReal) := CRealLt y x.
Definition CReal_appart (x y : CReal) := sum (CRealLt x y) (CRealLt y x).

Infix "<" := CRealLt : CReal_scope.
Infix ">" := CRealGt : CReal_scope.
Infix "#" := CReal_appart : CReal_scope.

(* This Prop can be extracted as a sigma type *)
Lemma CRealLtEpsilon : forall x y : CReal,
    CRealLtProp x y -> x < y.
Proof.
  intros x y H. unfold CRealLtProp in H.
  apply constructive_indefinite_ground_description_Z in H.
  - apply H.
  - intros n.
    pose proof Qlt_le_dec (2 * 2 ^ n) (seq y n - seq x n) as Hdec.
    destruct Hdec as [H1|H1].
    + left; exact H1.
    + right; apply Qle_not_lt in H1; exact H1.
Qed.

Lemma CRealLtForget : forall x y : CReal,
    x < y -> CRealLtProp x y.
Proof.
  intros. destruct H. exists x0. exact q.
Qed.

(* CRealLt is decided by the LPO in Type,
   which is a non-constructive oracle. *)
Lemma CRealLt_lpo_dec : forall x y : CReal,
    (forall (P : nat -> Prop), (forall n:nat, {P n} + {~P n})
                    -> {n | ~P n} + {forall n, P n})
    -> CRealLt x y + (CRealLt x y -> False).
Proof.
  intros x y lpo.
  destruct (lpo (fun n:nat =>
    seq y (Z_inj_nat_rev n) - seq x (Z_inj_nat_rev n) <= 2 * 2 ^ (Z_inj_nat_rev n)
  )).
  - intro n. destruct (Qlt_le_dec (2 * 2 ^ (Z_inj_nat_rev n))
                                  (seq y (Z_inj_nat_rev n) - seq x (Z_inj_nat_rev n))).
    + right; lra.
    + left; lra.
  - left; destruct s as [n nmaj]; exists (Z_inj_nat_rev n); lra.
  - right; intro abs; destruct abs as [n majn].
    specialize (q (Z_inj_nat n)).
    rewrite Z_inj_nat_id in q.
    pose proof (Qle_not_lt _ _ q). contradiction.
Qed.

(* Alias the large order *)
Definition CRealLe (x y : CReal) : Prop
  := CRealLt y x -> False.

Definition CRealGe (x y : CReal) := CRealLe y x.

Infix "<=" := CRealLe : CReal_scope.
Infix ">=" := CRealGe : CReal_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : CReal_scope.
Notation "x <= y < z"  := (prod (x <= y) (y < z)) : CReal_scope.
Notation "x < y < z"   := (prod (x < y) (y < z)) : CReal_scope.
Notation "x < y <= z"  := (prod (x < y) (y <= z)) : CReal_scope.

(* Alias the quotient order equality *)
Definition CRealEq (x y : CReal) : Prop
  := (CRealLe y x) /\ (CRealLe x y).

Infix "==" := CRealEq : CReal_scope.

Lemma CRealLe_not_lt : forall x y : CReal,
    (forall n : Z, (seq x n - seq y n <= 2 * 2 ^ n)%Q)
    <-> x <= y.
Proof.
  intros. split.
  - intros H H0.
    destruct H0 as [n H0]; specialize (H n); lra.
  - intros H n.
    destruct (Qlt_le_dec (2 * 2 ^ n) (seq x n - seq y n)).
    + exfalso. apply H. exists n. assumption.
    + assumption.
Qed.

Lemma CRealEq_diff : forall (x y : CReal),
    CRealEq x y
    <-> forall n:Z, ((Qabs (seq x n - seq y n)) <= (2 * 2 ^ n))%Q.
Proof.
  intros x y; split.
  - intros H n; destruct H as [Hyx Hxy].
    pose proof (CRealLe_not_lt x y) as [_ Hxy']. specialize (Hxy' Hxy n).
    pose proof (CRealLe_not_lt y x) as [_ Hyx']. specialize (Hyx' Hyx n).
    apply Qabs_Qle_condition; lra.
  - intros H; split;
      apply CRealLe_not_lt; intro n; specialize (H n);
      apply Qabs_Qle_condition in H; lra.
Qed.

(** If the elements x(n) and y(n) of two Cauchy sequences x and are apart by
    at least 2*eps(n), we can find a k such that all further elements of
    the sequences are apart by at least 2*eps(k) *)

Lemma CRealLt_aboveSig : forall (x y : CReal) (n : Z),
    (2 * 2^n < seq y n - seq x n)%Q
 -> let (k, _) := QarchimedeanExp2_Z (/(seq y n - seq x n - (2 * 2 ^ n)%Q))
    in forall p:Z,
        (p <= n)%Z
     -> (2^(-k) < seq y p - seq x p)%Q.
Proof.
  intros x y n maj.
  destruct (QarchimedeanExp2_Z (/((seq y) n - (seq x) n - (2*2^n)%Q))) as [k kmaj].
  intros p Hp.
  apply Qinv_lt_contravar in kmaj.
    3: apply Qpower_0_lt; lra.
    2: apply Qinv_lt_0_compat; lra.
  rewrite Qinv_involutive, <- Qpower_opp in kmaj; clear maj.
  pose proof ((cauchy x) n n p ltac:(lia) ltac:(lia)) as HCSx.
  pose proof ((cauchy y) n p n ltac:(lia) ltac:(lia)) as HCSy.
  rewrite Qabs_Qlt_condition in HCSx, HCSy.
  lra.
Qed.

(** This is a weakened form of CRealLt_aboveSig which a special shape of eps needed below *)

Lemma CRealLt_aboveSig' : forall (x y : CReal) (n : Z),
    (2 * 2^n < seq y n - seq x n)%Q
 -> let (k, _) := QarchimedeanExp2_Z (/(seq y n - seq x n - (2 * 2 ^ n)%Q))
    in forall p:Z,
        (p <= n)%Z
     -> (2 * 2^(Z.min (-k-1) n) < seq y p - seq x p)%Q.
Proof.
  intros x y n Hapart.
  pose proof CRealLt_aboveSig x y n Hapart.
  destruct (QarchimedeanExp2_Z (/ (seq y n - seq x n - (2 * 2 ^ n))))
    as [k kmaj].
  intros p Hp; specialize (H p Hp).
  pose proof Qpower_le_compat_l 2 (Z.min (- k -1) n) (- k-1) (Z.le_min_l _ _) ltac:(lra) as H1.
  rewrite Qpower_minus_pos in H1.
  apply (Qmult_le_compat_r _ _ 2) in H1.
  2: lra.
  ring_simplify in H1.
  exact (Qle_lt_trans _ _ _ H1 H).
Qed.

Lemma CRealLt_above : forall (x y : CReal),
    CRealLt x y
    -> { n : Z | forall p : Z,
          (p <= n)%Z -> (2 * 2 ^ n < seq y p - seq x p)%Q }.
Proof.
  intros x y [n maj].
  pose proof (CRealLt_aboveSig' x y n maj) as H.
  destruct (QarchimedeanExp2_Z (/ (seq y n - seq x n - (2 * 2 ^ n))))
    as [k kmaj].
  exists (Z.min (-k - 1) n)%Z; intros p Hp.
  apply H.
  lia.
Qed.

(* The CRealLt index separates the Cauchy sequences *)
Lemma CRealLt_above_same : forall (x y : CReal) (n : Z),
    (2 * 2 ^ n < seq y n - seq x n)%Q
 -> forall p:Z, (p <= n)%Z -> Qlt (seq x p) (seq y p).
Proof.
  intros x y n inf p H.
  simpl in inf |- *.
  pose proof ((cauchy x) n p n ltac:(lia) ltac:(lia)).
  pose proof ((cauchy y) n p n ltac:(lia) ltac:(lia)).
  rewrite Qabs_Qlt_condition in *.
  lra.
Qed.

Lemma CRealLt_asym : forall x y : CReal, x < y -> x <= y.
Proof.
  intros x y H [n q].
  apply CRealLt_above in H. destruct H as [p H].
  pose proof (CRealLt_above_same y x n q).
  apply (Qlt_not_le (seq y (Z.min n p))
                    (seq x (Z.min n p))).
  - apply H0. apply Z.le_min_l.
  - apply Qlt_le_weak. apply (Qplus_lt_l _ _ (-seq x (Z.min n p))).
    rewrite Qplus_opp_r. apply (Qlt_trans _ (2*2^p)).
    + pose proof Qpower_0_lt 2 p ltac:(lra). lra.
    + apply H. lia.
      (* ToDo: use lra *)
Qed.

Lemma CRealLt_irrefl : forall x:CReal, x < x -> False.
Proof.
  intros x abs. exact (CRealLt_asym x x abs abs).
Qed.

Lemma CRealLe_refl : forall x : CReal, x <= x.
Proof.
  intros. intro abs.
  pose proof (CRealLt_asym x x abs). contradiction.
Qed.

Lemma CRealEq_refl : forall x : CReal, x == x.
Proof.
  intros. split; apply CRealLe_refl.
Qed.

Lemma CRealEq_sym : forall x y : CReal, CRealEq x y -> CRealEq y x.
Proof.
  intros. destruct H. split; intro abs; contradiction.
Qed.

Lemma CRealLt_dec : forall x y z : CReal,
    x < y -> sum (x < z) (z < y).
Proof.
  intros x y z [n inf].
  destruct (QarchimedeanExp2_Z (/((seq y) n - (seq x) n - (2 * 2 ^ n)))) as [k kmaj].
  rewrite Qinv_lt_contravar, Qinv_involutive, <- Qpower_opp in kmaj.
    3: apply Qpower_0_lt; lra.
    2: apply Qinv_lt_0_compat; lra.

  destruct (Qlt_le_dec ((1#2) * ((seq y) n + (seq x) n)) ((seq z) (Z.min n (- k - 2))))
    as [Hxyltz|Hzlexy]; [left; pose (cauchy x) as HCS|right; pose (cauchy y) as HCS].

  all: exists (Z.min (n)%Z (-k - 2))%Z.
  all: specialize (HCS n n (Z.min n (-k-2))%Z ltac:(lia) ltac:(lia)).
  all: rewrite Qabs_Qlt_condition in HCS.
  all: assert (2 ^ Z.min n (- k - 2) <= 2 ^ (- k - 2))%Q as Hpowmin
         by (apply Qpower_le_compat_l; [lia|lra]).
  all: rewrite Qpower_minus_pos in Hpowmin; lra.
Qed.

Definition linear_order_T x y z := CRealLt_dec x z y.

Lemma CReal_le_lt_trans : forall x y z : CReal,
    x <= y -> y < z -> x < z.
Proof.
  intros x y z Hle Hlt.
  destruct (linear_order_T y x z Hlt) as [Hyltx|Hxltz].
  - contradiction.
  - exact Hxltz.
Qed.

Lemma CReal_lt_le_trans : forall x y z : CReal,
    x < y -> y <= z -> x < z.
Proof.
  intros x y z Hlt Hle.
  destruct (linear_order_T x z y Hlt) as [Hxltz|Hzlty].
  - exact Hxltz.
  - contradiction.
Qed.

Lemma CReal_le_trans : forall x y z : CReal,
    x <= y -> y <= z -> x <= z.
Proof.
  intros x y z Hxley Hylez contra.
  apply Hylez.
  apply (CReal_lt_le_trans _ x); assumption.
Qed.

Lemma CReal_lt_trans : forall x y z : CReal,
    x < y -> y < z -> x < z.
Proof.
  intros x y z Hxlty Hyltz.
  apply (CReal_lt_le_trans _ y _ Hxlty).
  apply CRealLt_asym; exact Hyltz.
Qed.

Lemma CRealEq_trans : forall x y z : CReal,
    CRealEq x y -> CRealEq y z -> CRealEq x z.
Proof.
  intros x y z Hxeqy Hyeqz.
  destruct Hxeqy as [Hylex Hxley].
  destruct Hyeqz as [Hzley Hylez].
  split.
  - intro contra. destruct (CRealLt_dec _ _ y contra); contradiction.
  - intro contra. destruct (CRealLt_dec _ _ y contra); contradiction.
Qed.

Add Parametric Relation : CReal CRealEq
    reflexivity proved by CRealEq_refl
    symmetry proved by CRealEq_sym
    transitivity proved by CRealEq_trans
      as CRealEq_rel.

#[global]
Instance CRealEq_relT : CRelationClasses.Equivalence CRealEq.
Proof.
  split.
  - exact CRealEq_refl.
  - exact CRealEq_sym.
  - exact CRealEq_trans.
Qed.

#[global]
Instance CRealLt_morph
  : CMorphisms.Proper
      (CMorphisms.respectful CRealEq (CMorphisms.respectful CRealEq CRelationClasses.iffT)) CRealLt.
Proof.
  intros x y Hxeqy x0 y0 Hx0eqy0.
  destruct Hxeqy as [Hylex Hxley].
  destruct Hx0eqy0 as [Hy0lex0 Hx0ley0].
  split.
  - intro Hxltx0; destruct (CRealLt_dec x x0 y).
    + assumption.
    + contradiction.
    + destruct (CRealLt_dec y x0 y0).
      * assumption.
      * assumption.
      * contradiction.
  - intro Hylty0; destruct (CRealLt_dec y y0 x).
    + assumption.
    + contradiction.
    + destruct (CRealLt_dec x y0 x0).
      * assumption.
      * assumption.
      * contradiction.
Qed.

#[global]
Instance CRealGt_morph
  : CMorphisms.Proper
      (CMorphisms.respectful CRealEq (CMorphisms.respectful CRealEq CRelationClasses.iffT)) CRealGt.
Proof.
  intros x y Hxeqy x0 y0 Hx0eqy0. apply CRealLt_morph; assumption.
Qed.

#[global]
Instance CReal_appart_morph
  : CMorphisms.Proper
      (CMorphisms.respectful CRealEq (CMorphisms.respectful CRealEq CRelationClasses.iffT)) CReal_appart.
Proof.
  intros x y Hxeqy x0 y0 Hx0eqy0.
  split.
  - intros Hapart. destruct Hapart as [Hxltx0|Hx0ltx].
    + left. rewrite <- Hx0eqy0, <- Hxeqy. exact Hxltx0.
    + right. rewrite <- Hx0eqy0, <- Hxeqy. exact Hx0ltx.
  - intros Hapart. destruct Hapart as [Hylty0|Hy0lty].
    + left. rewrite Hx0eqy0, Hxeqy. exact Hylty0.
    + right. rewrite Hx0eqy0, Hxeqy. exact Hy0lty.
Qed.

Add Parametric Morphism : CRealLtProp
    with signature CRealEq ==> CRealEq ==> iff
      as CRealLtProp_morph.
Proof.
  intros x y Hxeqy x0 y0 Hx0eqy0.
  split.
  - intro Hxltpx0. apply CRealLtForget. apply CRealLtEpsilon in Hxltpx0.
    rewrite <- Hxeqy, <- Hx0eqy0. exact Hxltpx0.
  - intro Hylty0. apply CRealLtForget. apply CRealLtEpsilon in Hylty0.
    rewrite Hxeqy, Hx0eqy0. exact Hylty0.
Qed.

Add Parametric Morphism : CRealLe
    with signature CRealEq ==> CRealEq ==> iff
      as CRealLe_morph.
Proof.
  intros x y Hxeqy x0 y0 Hx0eqy0.
  split.
  - intros Hxlex0 Hyley0. unfold CRealLe in Hxlex0.
    rewrite <- Hx0eqy0 in Hyley0. rewrite <- Hxeqy in Hyley0. contradiction.
  - intros Hxlex0 Hyley0. unfold CRealLe in Hxlex0.
    rewrite Hx0eqy0 in Hyley0. rewrite Hxeqy in Hyley0. contradiction.
Qed.

Add Parametric Morphism : CRealGe
    with signature CRealEq ==> CRealEq ==> iff
      as CRealGe_morph.
Proof.
  intros x y Hxeqy x0 y0 Hx0eqy0.
  unfold CRealGe. apply CRealLe_morph; assumption.
Qed.

Lemma CRealLt_proper_l : forall x y z : CReal,
    CRealEq x y
    -> CRealLt x z -> CRealLt y z.
Proof.
  intros x y z Hxeqy Hxltz.
  apply (CRealLt_morph x y Hxeqy z z).
  - apply CRealEq_refl.
  - apply Hxltz.
Qed.

Lemma CRealLt_proper_r : forall x y z : CReal,
    CRealEq x y
    -> CRealLt z x -> CRealLt z y.
Proof.
  intros x y z Hxeqy Hzltx.
  apply (CRealLt_morph z z (CRealEq_refl z) x y).
  - apply Hxeqy.
  - apply Hzltx.
Qed.

Lemma CRealLe_proper_l : forall x y z : CReal,
    CRealEq x y
    -> CRealLe x z -> CRealLe y z.
Proof.
  intros x y z Hxeqy Hxlez.
  apply (CRealLe_morph x y Hxeqy z z).
  - apply CRealEq_refl.
  - apply Hxlez.
Qed.

Lemma CRealLe_proper_r : forall x y z : CReal,
    CRealEq x y
    -> CRealLe z x -> CRealLe z y.
Proof.
  intros x y z Hxeqy Hzlex.
  apply (CRealLe_morph z z (CRealEq_refl z) x y).
  - apply Hxeqy.
  - apply Hzlex.
Qed.



(* Injection of Q into CReal *)

Lemma inject_Q_cauchy : forall q : Q, QCauchySeq (fun _ => q).
Proof.
  intros q k p r Hp Hr.
  apply Qabs_Qlt_condition.
  pose proof Qpower_0_lt 2 k; lra.
Qed.

Definition inject_Q (q : Q) : CReal :=
{|
  seq := (fun n : Z => q);
  scale := Qbound_ltabs_ZExp2 q;
  cauchy := inject_Q_cauchy q;
  bound := (fun _ : Z => Qbound_ltabs_ZExp2_spec q)
|}.

Definition inject_Z : Z -> CReal
  := fun n => inject_Q (n # 1).

Notation "0" := (inject_Q 0) : CReal_scope.
Notation "1" := (inject_Q 1) : CReal_scope.
Notation "2" := (inject_Q 2) : CReal_scope.

Lemma CRealLt_0_1 : CRealLt (inject_Q 0) (inject_Q 1).
Proof.
  exists (-2)%Z; cbn; lra.
Qed.

Lemma CReal_injectQPos : forall q : Q,
    (0 < q)%Q -> CRealLt (inject_Q 0) (inject_Q q).
Proof.
  intros q Hq. destruct (QarchimedeanExp2_Z ((2#1) / q)) as [k Hk].
  exists (-k)%Z; cbn.
  apply (Qmult_lt_compat_r _ _ q) in Hk.
    2: assumption.
  apply (Qmult_lt_compat_r _ _ (2^(-k))) in Hk.
    2: apply Qpower_0_lt; lra.
  field_simplify in Hk.
    2: lra.
  (* ToDo: field_simplify should collect powers - the next 3 lines ... *)
  rewrite <- Qmult_assoc, <- Qpower_plus in Hk by lra.
  ring_simplify (-k +k)%Z in Hk.
  rewrite Qpower_0_r in Hk.
  lra.
Qed.

Lemma inject_Q_compare : forall (x : CReal) (p : Z),
    x <= inject_Q (seq x p + (2^p)).
Proof.
  intros x p [n nmaj].
  cbn in nmaj.
  assert(2^n>0)%Q by (apply Qpower_0_lt; lra).
  assert(2^p>0)%Q by (apply Qpower_0_lt; lra).
  pose proof x.(cauchy) as xcau.
  destruct (Z.min_dec p n);
    [ specialize (xcau n n p ltac:(lia) ltac:(lia)) |
      specialize (xcau p n p ltac:(lia) ltac:(lia)) ].
  all: apply Qabs_Qlt_condition in xcau; lra.
Qed.

Add Parametric Morphism : inject_Q
    with signature Qeq ==> CRealEq
      as inject_Q_morph.
Proof.
  intros x y Heq; split.
  all: intros [n Hapart]; cbn in Hapart; rewrite Heq in Hapart.
  all: assert(2^n>0)%Q by (apply Qpower_0_lt; lra); lra.
Qed.

#[global]
Instance inject_Q_morph_T
  : CMorphisms.Proper
      (CMorphisms.respectful Qeq CRealEq) inject_Q.
Proof.
  intros x y Heq; split.
  all: intros [n Hapart]; cbn in Hapart; rewrite Heq in Hapart.
  all: assert(2^n>0)%Q by (apply Qpower_0_lt; lra); lra.
Qed.



(** * Algebraic operations *)

(** We reduce the rational numbers to accelerate calculations. *)
Definition CReal_plus_seq (x y : CReal) :=
  (fun n : Z => Qred (seq x (n-1)%Z + seq y (n-1)%Z)).

Definition CReal_plus_scale (x y : CReal) : Z :=
  Z.max x.(scale) y.(scale) + 1.

Lemma CReal_plus_cauchy : forall (x y : CReal),
  QCauchySeq (CReal_plus_seq x y).
Proof.
  intros x y n p q Hp Hq.
  unfold CReal_plus_seq.
  pose proof ((cauchy x) (n-1)%Z (p-1)%Z (q-1)%Z ltac:(lia) ltac:(lia)) as Hxbnd.
  pose proof ((cauchy y) (n-1)%Z (p-1)%Z (q-1)%Z ltac:(lia) ltac:(lia)) as Hybnd.
  do 2 rewrite Qred_correct.
  rewrite Qabs_Qlt_condition in Hxbnd, Hybnd |- *.
  rewrite Qpower_minus_pos in Hxbnd, Hybnd.
  lra.
Qed.

Lemma CReal_plus_bound : forall (x y : CReal),
  QBound (CReal_plus_seq x y) (CReal_plus_scale x y).
Proof.
  intros x y k.
  unfold CReal_plus_seq, CReal_plus_scale.
  pose proof (bound x (k-1)%Z) as Hxbnd.
  pose proof (bound y (k-1)%Z) as Hybnd.
  rewrite Qpower_plus by lra.
  pose proof Qpower_le_compat_l 2 (scale x) (Z.max (scale x) (scale y)) ltac:(lia) ltac:(lra) as Hxmax.
  pose proof Qpower_le_compat_l 2 (scale y) (Z.max (scale x) (scale y)) ltac:(lia) ltac:(lra) as Hymax.
  rewrite Qabs_Qlt_condition in Hxbnd, Hybnd |- *.
  rewrite Qred_correct.
  lra.
Qed.

Definition CReal_plus (x y : CReal) : CReal :=
{|
  seq := CReal_plus_seq x y;
  scale := CReal_plus_scale x y;
  cauchy := CReal_plus_cauchy x y;
  bound := CReal_plus_bound x y
|}.

Infix "+" := CReal_plus : CReal_scope.

Definition CReal_opp_seq (x : CReal) :=
  (fun n : Z => - seq x n).

Definition CReal_opp_scale (x : CReal) : Z :=
  x.(scale).

Lemma CReal_opp_cauchy : forall (x : CReal),
  QCauchySeq (CReal_opp_seq x).
Proof.
  intros x n p q Hp Hq; unfold CReal_opp_seq.
  pose proof ((cauchy x) n p q ltac:(lia) ltac:(lia)) as Hxbnd.
  rewrite Qabs_Qlt_condition in Hxbnd |- *.
  lra.
Qed.

Lemma CReal_opp_bound : forall (x : CReal),
  QBound (CReal_opp_seq x) (CReal_opp_scale x).
Proof.
  intros x k.
  unfold CReal_opp_seq, CReal_opp_scale.
  pose proof (bound x k) as Hxbnd.
  rewrite Qabs_Qlt_condition in Hxbnd |- *.
  lra.
Qed.

Definition CReal_opp (x : CReal) : CReal :=
{|
  seq := CReal_opp_seq x;
  scale := CReal_opp_scale x;
  cauchy := CReal_opp_cauchy x;
  bound := CReal_opp_bound x
|}.

Notation "- x" := (CReal_opp x) : CReal_scope.

Definition CReal_minus (x y : CReal) : CReal
  := CReal_plus x (CReal_opp y).

Infix "-" := CReal_minus : CReal_scope.

(* ToDo: make a tactic for this *)
Lemma CReal_red_seq: forall (a : Z -> Q) (b : Z) (c : QCauchySeq a) (d : QBound a b),
  seq (mkCReal a b c d) = a.
Proof.
  reflexivity.
Qed.

Lemma CReal_plus_assoc : forall (x y z : CReal),
    (x + y) + z == x + (y + z).
Proof.
  intros x y z; apply CRealEq_diff; intro n.
  unfold CReal_plus, CReal_plus_seq. do 4 rewrite CReal_red_seq.
  do 4 rewrite Qred_correct.
  ring_simplify (n-1-1)%Z.
  pose proof ((cauchy x) (n-1)%Z (n-2)%Z (n-1)%Z ltac:(lia) ltac:(lia)) as Hxbnd.
  specialize ((cauchy z) (n-1)%Z (n-2)%Z (n-1)%Z ltac:(lia) ltac:(lia)) as Hzbnd.
  apply Qlt_le_weak.
  rewrite Qabs_Qlt_condition in Hxbnd, Hzbnd |- *.
  rewrite Qpower_minus_pos in Hxbnd, Hzbnd.
  lra.
Qed.

Lemma CReal_plus_comm : forall x y : CReal,
    x + y == y + x.
Proof.
  intros x y; apply CRealEq_diff; intros n.
  unfold CReal_plus, CReal_plus_seq. do 2 rewrite CReal_red_seq.
  do 2 rewrite Qred_correct.
  pose proof ((cauchy x) (n-1)%Z (n-1)%Z (n-1)%Z ltac:(lia) ltac:(lia)) as Hxbnd.
  pose proof ((cauchy y) (n-1)%Z (n-1)%Z (n-1)%Z ltac:(lia) ltac:(lia)) as Hybnd.
  apply Qlt_le_weak.
  rewrite Qabs_Qlt_condition in Hxbnd, Hybnd |- *.
  rewrite Qpower_minus_pos in Hxbnd, Hybnd.
  lra.
Qed.

Lemma CReal_plus_0_l : forall r : CReal,
    inject_Q 0 + r == r.
Proof.
  intros x; apply CRealEq_diff; intros n.
  unfold CReal_plus, CReal_plus_seq, inject_Q. do 2 rewrite CReal_red_seq.
  rewrite Qred_correct.
  pose proof ((cauchy x) (n)%Z (n-1)%Z (n)%Z ltac:(lia) ltac:(lia)) as Hxbnd.
  apply Qlt_le_weak.
  rewrite Qabs_Qlt_condition in Hxbnd |- *.
  lra.
Qed.

Lemma CReal_plus_0_r : forall r : CReal,
    r + 0 == r.
Proof.
  intro r. rewrite CReal_plus_comm. apply CReal_plus_0_l.
Qed.

Lemma CReal_plus_lt_compat_l :
  forall x y z : CReal, y < z -> x + y < x + z.
Proof.
  intros  x y z Hlt.
  apply CRealLt_above in Hlt; destruct Hlt as [n Hapart]; exists n.
  unfold CReal_plus, CReal_plus_seq in Hapart |- *. do 2 rewrite CReal_red_seq.
  do 2 rewrite Qred_correct.
  specialize (Hapart (n-1)%Z ltac:(lia)).
  lra.
Qed.

Lemma CReal_plus_lt_compat_r :
  forall x y z : CReal, y < z -> y + x < z + x.
Proof.
  intros x y z.
  do 2 rewrite <- (CReal_plus_comm x).
  apply CReal_plus_lt_compat_l.
Qed.

Lemma CReal_plus_lt_reg_l :
  forall x y z : CReal, x + y < x + z -> y < z.
Proof.
  intros x y z Hlt.
  destruct Hlt as [n maj]; exists (n - 1)%Z.
  setoid_replace (seq z (n - 1)%Z - seq y (n - 1)%Z)%Q
    with (seq (CReal_plus x z) n - seq (CReal_plus x y) n)%Q.
  - rewrite Qpower_minus_pos.
    assert (2 ^ n > 0)%Q by (apply Qpower_0_lt; lra); lra.
  - unfold CReal_plus, CReal_plus_seq in maj |- *.
    do 2 rewrite CReal_red_seq in maj |- *.
    do 2 rewrite Qred_correct; ring.
Qed.

Lemma CReal_plus_lt_reg_r :
  forall x y z : CReal, y + x < z + x -> y < z.
Proof.
  intros x y z Hlt.
  rewrite (CReal_plus_comm y), (CReal_plus_comm z) in Hlt.
  apply CReal_plus_lt_reg_l in Hlt; exact Hlt.
Qed.

Lemma CReal_plus_le_reg_l :
  forall x y z : CReal, x + y <= x + z -> y <= z.
Proof.
  intros x y z Hlt contra.
  apply Hlt.
  apply CReal_plus_lt_compat_l; exact contra.
Qed.

Lemma CReal_plus_le_reg_r :
  forall x y z : CReal, y + x <= z + x -> y <= z.
Proof.
  intros x y z Hlt contra.
  apply Hlt.
  apply CReal_plus_lt_compat_r; exact contra.
Qed.

Lemma CReal_plus_le_compat_l : forall r r1 r2, r1 <= r2 -> r + r1 <= r + r2.
Proof.
  intros x y z Hlt contra.
  apply Hlt.
  apply CReal_plus_lt_reg_l in contra; exact contra.
Qed.

Lemma CReal_plus_le_lt_compat :
  forall r1 r2 r3 r4 : CReal, r1 <= r2 -> r3 < r4 -> r1 + r3 < r2 + r4.
Proof.
  intros r1 r2 r3 r4 Hr1ler2 Hr3ltr4.
  apply CReal_le_lt_trans with (r2 + r3).
  - intro contra; rewrite CReal_plus_comm, (CReal_plus_comm r1) in contra.
    apply CReal_plus_lt_reg_l in contra. contradiction.
  - apply CReal_plus_lt_compat_l. exact Hr3ltr4.
Qed.

Lemma CReal_plus_le_compat :
  forall r1 r2 r3 r4 : CReal, r1 <= r2 -> r3 <= r4 -> r1 + r3 <= r2 + r4.
Proof.
  intros r1 r2 r3 r4 Hr1ler2 Hr3ler4.
  apply CReal_le_trans with (r2 + r3).
  - intro contra; rewrite CReal_plus_comm, (CReal_plus_comm r1) in contra.
    apply CReal_plus_lt_reg_l in contra. contradiction.
  - apply CReal_plus_le_compat_l; exact Hr3ler4.
Qed.

Lemma CReal_plus_opp_r : forall x : CReal,
    x + - x == 0.
Proof.
  intros x; apply CRealEq_diff; intros n.
  unfold CReal_plus, CReal_plus_seq, CReal_opp, CReal_opp_seq, inject_Q.
  do 3 rewrite CReal_red_seq.
  rewrite Qred_correct.
  pose proof ((cauchy x) (n)%Z (n-1)%Z (n)%Z ltac:(lia) ltac:(lia)) as Hxbnd.
  apply Qlt_le_weak.
  rewrite Qabs_Qlt_condition in Hxbnd |- *.
  lra.
Qed.

Lemma CReal_plus_opp_l : forall x : CReal,
    - x + x == 0.
Proof.
  intro x. rewrite CReal_plus_comm. apply CReal_plus_opp_r.
Qed.

Lemma CReal_plus_proper_r : forall x y z : CReal,
    CRealEq x y -> CRealEq (CReal_plus x z) (CReal_plus y z).
Proof.
  intros. apply (CRealEq_trans _ (CReal_plus z x)).
  - apply CReal_plus_comm.
  - apply (CRealEq_trans _ (CReal_plus z y)).
    2: apply CReal_plus_comm.
    split.
    + intro abs. apply CReal_plus_lt_reg_l in abs.
      destruct H. contradiction.
    + intro abs. apply CReal_plus_lt_reg_l in abs.
      destruct H. contradiction.
Qed.

Lemma CReal_plus_proper_l : forall x y z : CReal,
    CRealEq x y -> CRealEq (CReal_plus z x) (CReal_plus z y).
Proof.
  intros. split.
  - intro abs. apply CReal_plus_lt_reg_l in abs.
    destruct H. contradiction.
  - intro abs. apply CReal_plus_lt_reg_l in abs.
    destruct H. contradiction.
Qed.

Add Parametric Morphism : CReal_plus
    with signature CRealEq ==> CRealEq ==> CRealEq
      as CReal_plus_morph.
Proof.
  intros x y H z t H0. apply (CRealEq_trans _ (CReal_plus x t)).
  - destruct H0.
    split.
    + intro abs. apply CReal_plus_lt_reg_l in abs. contradiction.
    + intro abs. apply CReal_plus_lt_reg_l in abs. contradiction.
  - apply CReal_plus_proper_r. apply H.
Qed.

#[global]
Instance CReal_plus_morph_T
  : CMorphisms.Proper
      (CMorphisms.respectful CRealEq (CMorphisms.respectful CRealEq CRealEq)) CReal_plus.
Proof.
  intros x y H z t H0. apply (CRealEq_trans _ (CReal_plus x t)).
  - destruct H0.
    split.
    + intro abs. apply CReal_plus_lt_reg_l in abs. contradiction.
    + intro abs. apply CReal_plus_lt_reg_l in abs. contradiction.
  - apply CReal_plus_proper_r. apply H.
Qed.

Lemma CReal_plus_eq_reg_l : forall (r r1 r2 : CReal),
    r + r1 == r + r2 -> r1 == r2.
Proof.
  intros. destruct H. split.
  - intro abs. apply (CReal_plus_lt_compat_l r) in abs. contradiction.
  - intro abs. apply (CReal_plus_lt_compat_l r) in abs. contradiction.
Qed.

Lemma CReal_opp_0 : -0 == 0.
Proof.
  apply (CReal_plus_eq_reg_l 0).
  rewrite CReal_plus_0_r, CReal_plus_opp_r. reflexivity.
Qed.

Lemma CReal_opp_plus_distr : forall r1 r2, - (r1 + r2) == - r1 + - r2.
Proof.
  intros. apply (CReal_plus_eq_reg_l (r1+r2)).
  rewrite CReal_plus_opp_r, (CReal_plus_comm (-r1)), CReal_plus_assoc.
  rewrite <- (CReal_plus_assoc r2), CReal_plus_opp_r, CReal_plus_0_l.
  rewrite CReal_plus_opp_r. reflexivity.
Qed.

Lemma CReal_opp_involutive : forall x:CReal, --x == x.
Proof.
  intros. apply (CReal_plus_eq_reg_l (-x)).
  rewrite CReal_plus_opp_l, CReal_plus_opp_r. reflexivity.
Qed.

Lemma CReal_opp_gt_lt_contravar : forall r1 r2, r1 > r2 -> - r1 < - r2.
Proof.
  unfold CRealGt; intros.
  apply (CReal_plus_lt_reg_l (r2 + r1)).
  rewrite CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_r.
  rewrite CReal_plus_comm, <- CReal_plus_assoc, CReal_plus_opp_l.
  rewrite CReal_plus_0_l. exact H.
Qed.

Lemma CReal_opp_ge_le_contravar : forall r1 r2, r1 >= r2 -> - r1 <= - r2.
Proof.
  intros. intro abs. apply H. clear H.
  apply (CReal_plus_lt_reg_r (-r1-r2)).
  unfold CReal_minus. rewrite <- CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_l.
  rewrite (CReal_plus_comm (-r1)), <- CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_l.
  exact abs.
Qed.

Lemma inject_Q_plus : forall q r : Q,
    inject_Q (q + r) == inject_Q q + inject_Q r.
Proof.
  intros q r.
  split.
  all: intros [n nmaj]; unfold CReal_plus, CReal_plus_seq, inject_Q in nmaj.
  all: do 4 rewrite CReal_red_seq in nmaj.
  all: rewrite Qred_correct in nmaj.
  all: assert(2^n>0)%Q by (apply Qpower_0_lt; lra); lra.
Qed.

Lemma inject_Q_one : inject_Q 1 == 1.
Proof.
  split.
  all: intros [n nmaj]; cbn in nmaj.
  all: assert(2^n>0)%Q by (apply Qpower_0_lt; lra); lra.
Qed.

Lemma inject_Q_lt : forall q r : Q,
    Qlt q r -> inject_Q q < inject_Q r.
Proof.
  intros q r Hlt.
  destruct (QarchimedeanExp2_Z (/(r-q))) as [n Hn].
  rewrite Qinv_lt_contravar, Qinv_involutive, <- Qpower_opp in Hn.
  - exists (-n-1)%Z; cbn.
    rewrite Qpower_minus_pos; lra.
  - apply Qlt_shift_inv_l; lra.
  - apply Qpower_0_lt; lra.
Qed.

Lemma opp_inject_Q : forall q : Q,
    inject_Q (-q) == - inject_Q q.
Proof.
  intros q.
  split.
  all: intros [n maj]; cbn in maj.
  all: unfold CReal_opp_seq, inject_Q in maj.
  all: rewrite CReal_red_seq in maj.
  all: assert(2^n>0)%Q by (apply Qpower_0_lt; lra); lra.
Qed.

Lemma lt_inject_Q : forall q r : Q,
    inject_Q q < inject_Q r -> (q < r)%Q.
Proof.
  intros q r [n Hn]; cbn in Hn.
  apply Qlt_minus_iff.
  assert(2^n>0)%Q by (apply Qpower_0_lt; lra); lra.
Qed.

Lemma le_inject_Q : forall q r : Q,
    inject_Q q <= inject_Q r -> (q <= r)%Q.
Proof.
  intros q r Hle.
  destruct (Qlt_le_dec r q) as [Hdec|Hdec].
  - exfalso.
    apply Hle; apply inject_Q_lt; exact Hdec.
  - exact Hdec.
Qed.

Lemma inject_Q_le : forall q r : Q,
    (q <= r)%Q -> inject_Q q <= inject_Q r.
Proof.
  intros q r Hle [n maj]; cbn in maj.
  assert(2^n>0)%Q by (apply Qpower_0_lt; lra); lra.
Qed.

Lemma inject_Z_plus : forall q r : Z,
    inject_Z (q + r) == inject_Z q + inject_Z r.
Proof.
  intros q r; unfold inject_Z.
  setoid_replace (q + r # 1)%Q with ((q#1) + (r#1))%Q.
  - apply inject_Q_plus.
  - rewrite Qinv_plus_distr; reflexivity.
Qed.

Lemma opp_inject_Z : forall n : Z,
    inject_Z (-n) == - inject_Z n.
Proof.
  intros n; unfold inject_Z.
  setoid_replace (-n # 1)%Q with (-(n#1))%Q.
  - rewrite opp_inject_Q; reflexivity.
  - reflexivity.
Qed.
