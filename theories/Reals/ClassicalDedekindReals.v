(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Stdlib.Logic.Eqdep_dec.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.HLevels.
Require Import QArith.
Require Import Qabs.
Require Import ConstructiveCauchyReals.
Require Import ConstructiveRcomplete.
Require Import Lia.
Require Import Lqa.
Require Import Qpower.
Require Import QExtra.
Require Import Znat.
Require Import ZArith_dec.
Require CMorphisms.

(*****************************************************************************)
(** * Q Auxiliary Lemmas                                                     *)
(*****************************************************************************)

(*
Fixpoint PosPow2_nat (n : nat) : positive :=
  match n with
  | O => 1
  | S n' => 2 * (PosPow2_nat n')
  end.

Local Lemma Qpower_2_neg_eq_pospow_inv : forall n : nat,
    (2 ^ (- Z.of_nat n) == 1#(PosPow2_nat n)%positive)%Q.
Proof.
  intros n; induction n.
  - reflexivity.
  - change (PosPow2_nat (S n)) with (2*(PosPow2_nat n))%positive.
    rewrite <- Qmult_frac_l.
    rewrite Nat2Z.inj_succ, Z.opp_succ, <- Z.sub_1_r.
    rewrite Qpower_minus_pos.
    change ((1 # 2) ^ 1)%Q with (1 # 2)%Q.
    rewrite Qmult_comm, IHn; reflexivity.
Qed.
*)

Local Lemma Qpower_2_neg_eq_natpow_inv : forall n : nat,
    (2 ^ (- Z.of_nat n) == 1#(Pos.of_nat (2^n)%nat))%Q.
Proof.
  intros n; induction n.
  - reflexivity.
  - rewrite Nat.pow_succ_r'.
    rewrite Nat2Pos.inj_mul.
    3: apply Nat.pow_nonzero; intros contra; inversion contra.
    2: intros contra; inversion contra.
    change (Pos.of_nat 2)%nat with 2%positive.
    rewrite Qmult_frac_l.
    rewrite Nat2Z.inj_succ, Z.opp_succ, <- Z.sub_1_r.
    rewrite Qpower_minus_pos.
    change ((1 # 2) ^ 1)%Q with (1 # 2)%Q.
    rewrite Qmult_comm, IHn; reflexivity.
Qed.


Local Lemma Qpower_2_invneg_le_pow : forall n : Z,
    (1 # Pos.of_nat (2 ^ Z.to_nat (- n)) <= 2 ^ n)%Q.
Proof.
  intros n; destruct n.
  - intros contra; inversion contra.
  - (* ToDo: find out why this works - somehow 1#(...) seems to be coereced to 1 *)
    apply (Qpower_1_le_pos 2 p ltac:(lra)).
  - rewrite <- Qpower_2_neg_eq_natpow_inv.
    rewrite Z2Nat.id by lia.
    rewrite Z.opp_involutive.
    apply Qle_refl.
Qed.

Local Lemma Qpower_2_neg_le_one : forall n : nat,
    (2 ^ (- Z.of_nat n) <= 1)%Q.
Proof.
  intros n; induction n.
  - intros contra; inversion contra.
  - rewrite Nat2Z.inj_succ, Z.opp_succ, <- Z.sub_1_r.
    rewrite Qpower_minus_pos.
    lra.
Qed.

(*****************************************************************************)
(** * Dedekind cuts                                                          *)
(*****************************************************************************)

(** ** Definition *)

(**
   Classical Dedekind reals. With the 3 logical axioms funext,
   sig_forall_dec and sig_not_dec, the lower cuts defined as
   functions Q -> bool have all the classical properties of the
   real numbers.

   We could prove operations and theorems about them directly,
   but instead we notice that they are a quotient of the
   constructive Cauchy reals, from which they inherit many properties.
*)

(* The limited principle of omniscience *)
Axiom sig_forall_dec
  : forall (P : nat -> Prop),
    (forall n, {P n} + {~P n})
    -> {n | ~P n} + {forall n, P n}.

Axiom sig_not_dec : forall P : Prop, { ~~P } + { ~P }.

(* Try to find a surjection CReal -> lower cuts. *)
Definition isLowerCut (f : Q -> bool) : Prop
  := (forall q r:Q, Qle q r -> f r = true -> f q = true) (* interval *)
     /\ ~(forall q:Q, f q = true) (* avoid positive infinity *)
     /\ ~(forall q:Q, f q = false) (* avoid negative infinity *)
     (* openness, the cut contains rational numbers
        strictly lower than a real number. *)
     /\ (forall q:Q, f q = true -> ~(forall r:Q, Qle r q \/ f r = false)).

(** ** Properties *)

Lemma isLowerCut_hprop : forall (f : Q -> bool),
    IsHProp (isLowerCut f).
Proof.
  intro f. apply and_hprop.
  2: apply and_hprop. 2: apply not_hprop.
  2: apply and_hprop. 2: apply not_hprop.
  - apply forall_hprop. intro x.
    apply forall_hprop. intro y.
    apply impl_hprop. apply impl_hprop.
    intros p q. apply eq_proofs_unicity_on.
    intro b. destruct (f x), b.
    + left. reflexivity.
    + right. discriminate.
    + right. discriminate.
    + left. reflexivity.
  - apply forall_hprop. intro q. apply impl_hprop. apply not_hprop.
Qed.

Lemma lowerCutBelow : forall f : Q -> bool,
    isLowerCut f -> { q : Q | f q = true }.
Proof.
  intros.
  destruct (sig_forall_dec (fun n:nat => f (-(Z.of_nat n # 1))%Q = false)).
  - intro n. destruct (f (-(Z.of_nat n # 1))%Q).
    + right. discriminate.
    + left. reflexivity.
  - destruct s. exists (-(Z.of_nat x # 1))%Q.
    destruct (f (-(Z.of_nat x # 1))%Q).
    + reflexivity.
    + exfalso. apply n. reflexivity.
  - exfalso. destruct H, H0, H1. apply H1. intro q.
    destruct (f q) eqn:des. 2: reflexivity. exfalso.
    destruct (Qarchimedean (-q)) as [p pmaj].
    rewrite <- (Qplus_lt_l _ _ (q-(Z.pos p # 1))) in pmaj.
    ring_simplify in pmaj.
    specialize (H (- (Z.pos p#1))%Q q).
    specialize (e (Pos.to_nat p)).
    rewrite positive_nat_Z in e. rewrite H in e.
    + discriminate.
    + ring_simplify. apply Qlt_le_weak, pmaj.
    + exact des.
Qed.

Lemma lowerCutAbove : forall f : Q -> bool,
    isLowerCut f -> { q : Q | f q = false }.
Proof.
  intros.
  destruct (sig_forall_dec (fun n => f (Z.of_nat n # 1)%Q = true)).
  - intro n. destruct (f (Z.of_nat n # 1)%Q).
    + left. reflexivity.
    + right. discriminate.
  - destruct s. exists (Z.of_nat x # 1)%Q. destruct (f (Z.of_nat x # 1)%Q).
    + exfalso. apply n. reflexivity.
    + reflexivity.
  - exfalso. destruct H, H0, H1. apply H0. intro q.
    destruct (Qarchimedean q) as [p pmaj].
    apply (H q (Z.of_nat (Pos.to_nat p) # 1)%Q).
    + rewrite positive_nat_Z. apply Qlt_le_weak, pmaj.
    + apply e.
Qed.

Lemma lowerUpper : forall (f : Q -> bool) (q r : Q),
    isLowerCut f -> Qle q r -> f q = false -> f r = false.
Proof.
  intros. destruct H. specialize (H q r H0). destruct (f r) eqn:desR.
  2: reflexivity. exfalso. specialize (H (eq_refl _)).
  rewrite H in H1. discriminate.
Qed.

Lemma UpperAboveLower : forall (f : Q -> bool) (q r : Q),
    isLowerCut f
    -> f q = true
    -> f r = false
    -> Qlt q r.
Proof.
  intros. destruct H. apply Qnot_le_lt. intro abs.
  rewrite (H r q abs) in H1.
  - discriminate.
  - exact H0.
Qed.

(*****************************************************************************)
(** * Classical Dedekind reals                                               *)
(*****************************************************************************)

(** ** Definition *)

Definition DReal : Set
  := { f : Q -> bool | isLowerCut f }.

(** ** Induction principle *)

Fixpoint DRealQlim_rec (f : Q -> bool) (low : isLowerCut f) (n p : nat) { struct p }
  : f (proj1_sig (lowerCutBelow f low) + (Z.of_nat p # Pos.of_nat (S n)))%Q = false
    -> { q : Q | f q = true /\ f (q + (1 # Pos.of_nat (S n)))%Q = false }.
Proof.
  intros. destruct p.
  - exfalso. destruct (lowerCutBelow f low); unfold proj1_sig in H.
    destruct low. rewrite (H0 _ x) in H.
    + discriminate.
    + simpl.
      apply (Qplus_le_l _ _ (-x)). ring_simplify. discriminate.
    + exact e.
  - destruct (f (proj1_sig (lowerCutBelow f low) + (Z.of_nat p # Pos.of_nat (S n)))%Q) eqn:des.
    + exists (proj1_sig (lowerCutBelow f low) + (Z.of_nat p # Pos.of_nat (S n)))%Q.
      split.
      * exact des.
      * destruct (f (proj1_sig (lowerCutBelow f low)
                     + (Z.of_nat p # Pos.of_nat (S n)) + (1 # Pos.of_nat (S n)))%Q) eqn:d.
        2: reflexivity. exfalso.
        destruct low.
        rewrite (e _ (proj1_sig (lowerCutBelow f (conj e a)) + (Z.of_nat p # Pos.of_nat (S n)) + (1 # Pos.of_nat (S n))))%Q in H.
        -- discriminate.
        -- rewrite <- Qplus_assoc, Qplus_le_r.
           rewrite Qinv_plus_distr.
           replace (Z.of_nat p + 1)%Z with (Z.of_nat (S p))%Z.
           ++ apply Qle_refl.
           ++ replace 1%Z with (Z.of_nat 1).
              ** rewrite <- (Nat2Z.inj_add p 1).
                 apply f_equal. rewrite Nat.add_comm. reflexivity.
              ** reflexivity.
        -- exact d.
    + destruct (DRealQlim_rec f low n p des) as [q qmaj].
      exists q. exact qmaj.
Qed.

(** ** Conversion to and from constructive Cauchy real CReal *)

(** *** Conversion from CReal to DReal *)

Lemma DRealAbstr_aux :
  forall x H,
  isLowerCut (fun q : Q =>
    if sig_forall_dec (fun n : nat => seq x (- Z.of_nat n) <= q + 2 ^ (- Z.of_nat n)) (H q)
    then true else false).
Proof.
  repeat split.
  - intros.
    destruct (sig_forall_dec (fun n : nat => (seq x (-Z.of_nat n) <= q + (2^-Z.of_nat n))%Q)
                             (H q)).
    + reflexivity.
    + exfalso.
      destruct (sig_forall_dec (fun n : nat => (seq x (-Z.of_nat n) <= r + (2^-Z.of_nat n))%Q)
                               (H r)).
      * destruct s. apply n.
        apply (Qle_trans _ _ _ (q0 x0)).
        apply Qplus_le_l. exact H0.
      * discriminate.
  - intro abs. destruct (Rfloor x) as [z [_ zmaj]].
    specialize (abs (z+3 # 1)%Q).
    destruct (sig_forall_dec (fun n : nat => (seq x (-Z.of_nat n) <= (z+3 # 1) + (2^-Z.of_nat n))%Q)
                             (H (z+3 # 1)%Q)).
    2: exfalso; discriminate. clear abs. destruct s as [n nmaj]. apply nmaj.
    rewrite <- (inject_Q_plus (z#1) 2) in zmaj.
    apply CRealLt_asym in zmaj. rewrite <- CRealLe_not_lt in zmaj.
    specialize (zmaj (-Z.of_nat n)%Z).
    unfold inject_Q in zmaj; rewrite CReal_red_seq in zmaj.
    destruct x as [xn xcau]; rewrite CReal_red_seq in H, nmaj, zmaj |- *.
    rewrite Qinv_plus_distr in zmaj.
    apply (Qplus_le_l _ _ (-(z + 2 # 1))). apply (Qle_trans _ _ _ zmaj).
    apply (Qplus_le_l _ _ (-(2^-Z.of_nat n))). apply (Qle_trans _ 1).
    + ring_simplify. apply Qpower_2_neg_le_one.
    + ring_simplify. rewrite <- (Qinv_plus_distr z 3 1), <- (Qinv_plus_distr z 2 1). lra.
  - intro abs. destruct (Rfloor x) as [z [zmaj _]].
    specialize (abs (z-4 # 1)%Q).
    destruct (sig_forall_dec (fun n : nat => (seq x (-Z.of_nat n) <= (z-4 # 1) + (2^-Z.of_nat n))%Q)
                             (H (z-4 # 1)%Q)).
    + exfalso; discriminate.
    + clear abs.
      apply CRealLt_asym in zmaj. apply zmaj. clear zmaj.
      exists 0%Z. unfold inject_Q; rewrite CReal_red_seq.
      specialize (q O).
      destruct x as [xn xcau].
      rewrite CReal_red_seq in H, q |- *.
      unfold Z.of_nat in q.
      change (2 ^ (- 0))%Q with 1%Q in q. change (-0)%Z with 0%Z in q.
      rewrite <- Qinv_minus_distr in q.
      change (2^0)%Q with 1%Q.
      lra.
  - intros q H0 abs.
    destruct (sig_forall_dec (fun n : nat => (seq x (-Z.of_nat n) <= q + (2^-Z.of_nat n))%Q) (H q)).
    2: exfalso; discriminate. clear H0.
    destruct s as [n nmaj].
    (* We have that q < x as real numbers. The middle
       (q + xSn - 1/Sn)/2 is also lower than x, witnessed by the same index n. *)
    specialize (abs ((q + seq x (-Z.of_nat n) - (2^-Z.of_nat n)%Q)/2)%Q).
    destruct abs.
    + apply (Qmult_le_r _ _ 2) in H0.
      * field_simplify in H0.
        apply (Qplus_le_r _ _ ((2^-Z.of_nat n) - q)) in H0.
        ring_simplify in H0. apply nmaj. rewrite Qplus_comm. exact H0.
      * reflexivity.
    + destruct (sig_forall_dec
                  (fun n0 : nat =>
                     (seq x (-Z.of_nat n0) <= (q + seq x (-Z.of_nat n) - (2^-Z.of_nat n)) / 2 + (2^-Z.of_nat n0))%Q)
                  (H ((q + seq x (-Z.of_nat n) - (2^-Z.of_nat n)) / 2)%Q)).
      * discriminate.
      * clear H0. specialize (q0 n).
        apply (Qmult_le_l _ _ 2) in q0.
        -- field_simplify in q0.
           apply (Qplus_le_l _ _ (-seq x (-Z.of_nat n))) in q0. ring_simplify in q0.
           contradiction.
        -- reflexivity.
Qed.

Definition DRealAbstr : CReal -> DReal.
Proof.
  intro x.
  assert (forall (q : Q) (n : nat),
   {(fun n0 : nat => (seq x (-Z.of_nat n0) <= q + (2^-Z.of_nat n0))%Q) n} +
   {~ (fun n0 : nat => (seq x (-Z.of_nat n0) <= q + (2^-Z.of_nat n0))%Q) n}).
  { intros. destruct (Qlt_le_dec (q + (2^-Z.of_nat n)) (seq x (-Z.of_nat n))).
    - right. apply (Qlt_not_le _ _ q0).
    - left. exact q0. }

  exists (fun q:Q => if sig_forall_dec (fun n:nat => Qle (seq x (-Z.of_nat n)) (q + (2^-Z.of_nat n))) (H q)
             then true else false).
  apply DRealAbstr_aux.
Defined.

(** *** Conversion from DReal to CReal *)

Definition DRealQlim (x : DReal) (n : nat)
  : { q : Q | proj1_sig x q = true /\ proj1_sig x (q + (1# Pos.of_nat (S n)))%Q = false }.
Proof.
  destruct x as [f low].
  destruct (lowerCutAbove f low).
  destruct (Qarchimedean (x - proj1_sig (lowerCutBelow f low))) as [p pmaj].
  apply (DRealQlim_rec f low n ((S n) * Pos.to_nat p)).
  destruct (lowerCutBelow f low); unfold proj1_sig; unfold proj1_sig in pmaj.
  destruct (f (x0 + (Z.of_nat (S n * Pos.to_nat p) # Pos.of_nat (S n)))%Q) eqn:des.
  2: reflexivity. exfalso. destruct low.
  rewrite (H _ (x0 + (Z.of_nat (S n * Pos.to_nat p) # Pos.of_nat (S n)))%Q) in e.
  - discriminate.
  - setoid_replace (Z.of_nat (S n * Pos.to_nat p) # Pos.of_nat (S n))%Q with (Z.pos p # 1)%Q.
    + apply (Qplus_lt_l _ _ x0) in pmaj. ring_simplify in pmaj.
      apply Qlt_le_weak, pmaj.
    + rewrite Nat2Z.inj_mul, positive_nat_Z.
      unfold Qeq, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_comm.
      replace (Z.of_nat (S n)) with (Z.pos (Pos.of_nat (S n))).
      * reflexivity.
      * simpl. destruct n.
        -- reflexivity.
        -- apply f_equal.
           apply Pos.succ_of_nat. discriminate.
  - exact des.
Qed.

Definition DRealQlimExp2 (x : DReal) (n : nat)
  : { q : Q | proj1_sig x q = true /\ proj1_sig x (q + (1#(Pos.of_nat (2^n)%nat)))%Q = false }.
Proof.
  destruct (DRealQlim x (pred (2^n))%nat) as [q qmaj].
  exists q.
  rewrite Nat.succ_pred_pos in qmaj.
    2: apply Nat.neq_0_lt_0, Nat.pow_nonzero; intros contra; inversion contra.
  exact qmaj.
Qed.

Definition CReal_of_DReal_seq (x : DReal) (n : Z) :=
    proj1_sig (DRealQlimExp2 x (Z.to_nat (-n))).

Lemma CReal_of_DReal_cauchy (x : DReal) :
    QCauchySeq (CReal_of_DReal_seq x).
Proof.
  unfold QCauchySeq, CReal_of_DReal_seq.
  intros n k l Hk Hl.
  destruct (DRealQlimExp2 x (Z.to_nat (-k))) as [q Hq].
  destruct (DRealQlimExp2 x (Z.to_nat (-l))) as [r Hr].
  destruct x as [f Hflc].
  unfold proj1_sig in *.
  apply Qabs_case.
  - intros. apply (Qlt_le_trans _ (1 # Pos.of_nat (2 ^ Z.to_nat (-l)))).
    + apply (Qplus_lt_l _ _ r); ring_simplify.
      apply (UpperAboveLower f).
      * exact Hflc.
      * apply Hq.
      * apply Hr.
    + apply (Qle_trans _ _ _ (Qpower_2_invneg_le_pow _)).
      apply Qpower_le_compat_l; [lia|lra].
  - intros. apply (Qlt_le_trans _ (1 # Pos.of_nat (2 ^ Z.to_nat (-k)))).
    + apply (Qplus_lt_l _ _ q); ring_simplify.
      apply (UpperAboveLower f).
      * exact Hflc.
      * apply Hr.
      * apply Hq.
    + apply (Qle_trans _ _ _ (Qpower_2_invneg_le_pow _)).
      apply Qpower_le_compat_l; [lia|lra].
Qed.

Lemma CReal_of_DReal_seq_max_prec_1 : forall (x : DReal) (n : Z),
   (n>=0)%Z -> CReal_of_DReal_seq x n = CReal_of_DReal_seq x 0.
Proof.
  intros x n Hngt0.
  unfold CReal_of_DReal_seq.
  destruct n.
  - reflexivity.
  - reflexivity.
  - lia.
Qed.

Lemma CReal_of_DReal_seq_bound :
  forall (x : DReal) (i j : Z),
    (Qabs (CReal_of_DReal_seq x i - CReal_of_DReal_seq x j) <= 1)%Q.
Proof.
  intros x i j.
  pose proof CReal_of_DReal_cauchy x 0%Z as Hcau.
  apply Qlt_le_weak; change (2^0)%Q with 1%Q in Hcau.
  (* Either i, j are >= 0 in which case we can rewrite with CReal_of_DReal_seq_max_prec_1,
     or they are <0, in which case Hcau can be used immediately *)
  destruct (Z_gt_le_dec i 0) as [Hi|Hi];
  destruct (Z_gt_le_dec j 0) as [Hj|Hj].
  all: try rewrite (CReal_of_DReal_seq_max_prec_1 x i) by lia;
       try rewrite (CReal_of_DReal_seq_max_prec_1 x j) by lia;
       apply Hcau; lia.
  (* ToDo: check if for CReal_from_cauchy_seq_bound a similar simple proof is possible *)
Qed.

Definition CReal_of_DReal_scale (x : DReal) : Z :=
  Qbound_lt_ZExp2 (Qabs (CReal_of_DReal_seq x (-1)) + 2)%Q.

Lemma CReal_of_DReal_bound : forall (x : DReal),
  QBound (CReal_of_DReal_seq x) (CReal_of_DReal_scale x).
Proof.
  intros x n.
  unfold CReal_of_DReal_scale.

  (* Use the spec of Qbound_lt_ZExp2 to linearize the RHS *)
  apply (Qlt_trans_swap_hyp _ _ _ (Qbound_lt_ZExp2_spec _)).

  (* Massage the goal so that CReal_of_DReal_seq_bound can be applied *)
  apply (Qplus_lt_l _ _ (-Qabs (CReal_of_DReal_seq x (-1)))%Q); ring_simplify.
  assert(forall r s : Q, (r + -1*s == r-s)%Q) as Aux
    by (intros; lra); rewrite Aux; clear Aux.
  apply (Qle_lt_trans _ _ _ (Qabs_triangle_reverse _ _)).
  apply (Qle_lt_trans _ 1%Q _).
    2: lra.
  apply CReal_of_DReal_seq_bound.
Qed.

Definition DRealRepr (x : DReal) : CReal :=
{|
  seq := CReal_of_DReal_seq x;
  scale := CReal_of_DReal_scale x;
  cauchy := CReal_of_DReal_cauchy x;
  bound := CReal_of_DReal_bound x
|}.

(** ** Order for DReal *)

Definition Rle (x y : DReal)
  := forall q:Q, proj1_sig x q = true -> proj1_sig y q = true.

Lemma Rle_antisym : forall x y : DReal,
    Rle x y
    -> Rle y x
    -> x = y.
Proof.
  intros [f cf] [g cg] H H0. unfold Rle in H,H0; simpl in H, H0.
  assert (f = g).
  { apply functional_extensionality. intro q.
    specialize (H q). specialize (H0 q).
    destruct (f q), (g q).
    - reflexivity.
    - exfalso. specialize (H (eq_refl _)). discriminate.
    - exfalso. specialize (H0 (eq_refl _)). discriminate.
    - reflexivity. }
  subst g. replace cg with cf.
  - reflexivity.
  - apply isLowerCut_hprop.
Qed.

Lemma DRealOpen : forall (x : DReal) (q : Q),
    proj1_sig x q = true
    -> { r : Q | Qlt q r /\ proj1_sig x r = true }.
Proof.
  intros.
  destruct (sig_forall_dec (fun n => Qle (proj1_sig (DRealQlim x n)) q)).
  - intro n. destruct (DRealQlim x n); unfold proj1_sig.
    destruct (Qlt_le_dec q x0).
    + right. exact (Qlt_not_le _ _ q0).
    + left. exact q0.
  - destruct s. apply Qnot_le_lt in n.
    destruct (DRealQlim x x0); unfold proj1_sig in n.
    exists x1. split.
    + exact n.
    + apply a.
  - exfalso. destruct x as [f low]. unfold proj1_sig in H, q0.
    destruct low, a, a. apply (n1 q H). intros.
    destruct (Qlt_le_dec q r). 2: left; exact q1. right.
    destruct (Qarchimedean (/(r - q))) as [p pmaj].
    specialize (q0 (Pos.to_nat p)).
    destruct (DRealQlim (exist _ f (conj e (conj n (conj n0 n1)))) (Pos.to_nat p))
      as [s smaj].
    unfold proj1_sig in smaj.
    apply (lowerUpper f (s + (1 # Pos.of_nat (S (Pos.to_nat p))))).
    + exact (conj e (conj n (conj n0 n1))).
    + apply (Qle_trans _ (s + (r-q))).
      * apply Qplus_le_r. apply (Qle_trans _ (1 # p)).
        -- unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_l.
           apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
           rewrite Nat2Pos.id.
           ++ apply le_S, Nat.le_refl.
           ++ discriminate.
        -- apply (Qmult_le_l _ _ ( (Z.pos p # 1) / (r-q))).
           ++ rewrite <- (Qmult_0_r (Z.pos p #1)). apply Qmult_lt_l.
              ** reflexivity.
              ** apply Qinv_lt_0_compat.
                 unfold Qminus. rewrite <- Qlt_minus_iff. exact q1.
           ++ unfold Qdiv. rewrite Qmult_comm, <- Qmult_assoc.
              rewrite (Qmult_comm (/(r-q))), Qmult_inv_r, Qmult_assoc.
              ** setoid_replace ((1 # p) * (Z.pos p # 1))%Q with 1%Q.
                 2: reflexivity. rewrite Qmult_1_l, Qmult_1_r.
                 apply Qlt_le_weak, pmaj.
              ** intro abs. apply Qlt_minus_iff in q1.
                 rewrite abs in q1. apply (Qlt_not_le _ _ q1), Qle_refl.
      * apply (Qplus_le_l _ _ (q-r)). ring_simplify. exact q0.
    + apply smaj.
Qed.

Lemma DRealReprQ : forall (x : DReal) (q : Q),
    proj1_sig x q = true
    -> CRealLt (inject_Q q) (DRealRepr x).
Proof.
  intros x q H.

  (* expand and simplify goal and hypothesis *)
  destruct (DRealOpen x q H) as [r rmaj].
  destruct (QarchimedeanLowExp2_Z ((1#4)*(r - q))) as [p pmaj].
    1: lra.
  exists (p)%Z.
  destruct x as [f low]; unfold DRealRepr, CReal_of_DReal_seq, inject_Q; do 2 rewrite CReal_red_seq.
  destruct (DRealQlimExp2 (exist _ f low) (Z.to_nat (-p))) as [s smaj].
  unfold proj1_sig in smaj, rmaj, H |- * .
  rewrite <- (Qmult_lt_l _ _ 4%Q) in pmaj by lra.
  setoid_replace (4 * ((1 # 4) * (r - q)))%Q with (r-q)%Q in pmaj by ring.
  apply proj2 in rmaj.
  apply proj2 in smaj.

  (* Use the fact that s+eps is above the cut and r is below the cut.
     This limits the distance between s and r. *)
  pose proof UpperAboveLower f _ _ low rmaj smaj as Hrltse; clear rmaj smaj.
  pose proof Qpower_2_invneg_le_pow p as Hpowcut.
  pose proof Qpower_0_lt 2 p ltac:(lra) as Hpowpos.
  lra.
Qed.

Lemma DRealReprQup : forall (x : DReal) (q : Q),
    proj1_sig x q = false
    -> CRealLe (DRealRepr x) (inject_Q q).
Proof.
  intros x q H [p pmaj].

  (* expand and simplify goal and hypothesis *)
  unfold inject_Q, DRealRepr, CReal_of_DReal_seq in pmaj. do 2 rewrite CReal_red_seq in pmaj.
  destruct (DRealQlimExp2 x (Z.to_nat (- p))) as [r rmaj].
  destruct x as [f low].
  unfold proj1_sig in pmaj, rmaj, H.
  apply proj1 in rmaj.

  (* Use the fact that q is above the cut and r is below the cut. *)
  pose proof UpperAboveLower f _ _ low rmaj H as Hrltse.
  pose proof Qpower_0_lt 2 p ltac:(lra) as Hpowpos.
  lra.
Qed.

Lemma DRealQuot1 : forall x y:DReal, CRealEq (DRealRepr x) (DRealRepr y) -> x = y.
Proof.
  intros. destruct H. apply Rle_antisym.
  - clear H. intros q H1. destruct (proj1_sig y q) eqn:des.
    + reflexivity.
    + exfalso. apply H0.
      apply (CReal_le_lt_trans _ (inject_Q q)).
      * apply DRealReprQup.
        exact des.
      * apply DRealReprQ. exact H1.
  - clear H0. intros q H1. destruct (proj1_sig x q) eqn:des.
    + reflexivity.
    + exfalso. apply H.
      apply (CReal_le_lt_trans _ (inject_Q q)).
      * apply DRealReprQup.
        exact des.
      * apply DRealReprQ. exact H1.
Qed.

Lemma DRealAbstrFalse : forall (x : CReal) (q : Q) (n : nat),
    proj1_sig (DRealAbstr x) q = false
    -> (seq x (- Z.of_nat n) <= q + 2 ^ (- Z.of_nat n))%Q.
Proof.
  intros x q n H.
  unfold DRealAbstr, proj1_sig in H.
  match type of H with context [ if ?a then _ else _ ] => destruct a as [H'|H']end.
  - discriminate.
  - apply H'.
Qed.

(** For arbitrary n:Z, we need to relaxe the bound *)

Lemma DRealAbstrFalse' : forall (x : CReal) (q : Q) (n : Z),
    proj1_sig (DRealAbstr x) q = false
    -> (seq x n <= q + 2*2^n)%Q.
Proof.
  intros x q n H.
  unfold DRealAbstr, proj1_sig in H.
  match type of H with context [ if ?a then _ else _ ] => destruct a as [H'|H']end.
  - discriminate.
  - destruct (Z_le_gt_dec n 0) as [Hdec|Hdec].
    + specialize (H' (Z.to_nat (-n) )).
      rewrite (Z2Nat.id (-n)%Z ltac:(lia)), Z.opp_involutive in H'.
      pose proof Qpower_0_lt 2 n; lra.
    + specialize (H' (Z.to_nat (0) )). cbn in H'.
      pose proof cauchy x n%Z 0%Z n ltac:(lia) ltac:(lia) as Hxbnd.
      apply Qabs_Qlt_condition in Hxbnd.
      pose proof Qpower_1_le 2 n ltac:(lra) ltac:(lia).
      lra.
Qed.

Lemma DRealAbstrFalse'' : forall (x : CReal) (q : Q) (n : Z),
    proj1_sig (DRealAbstr x) q = false
    -> (seq x n <= q + 2^n + 1)%Q.
Proof.
  intros x q n H.
  unfold DRealAbstr, proj1_sig in H.
  match type of H with context [ if ?a then _ else _ ] => destruct a as [H'|H']end.
  - discriminate.
  - destruct (Z_le_gt_dec n 0) as [Hdec|Hdec].
    + specialize (H' (Z.to_nat (-n) )).
      rewrite (Z2Nat.id (-n)%Z ltac:(lia)), Z.opp_involutive in H'.
      pose proof Qpower_0_lt 2 n; lra.
    + specialize (H' (Z.to_nat (0) )). cbn in H'.
      pose proof cauchy x n%Z 0%Z n ltac:(lia) ltac:(lia) as Hxbnd.
      apply Qabs_Qlt_condition in Hxbnd.
      lra.
Qed.

Lemma DRealQuot2 : forall x:CReal, CRealEq (DRealRepr (DRealAbstr x)) x.
Proof.
  split.
  - intros [p pmaj].
    unfold DRealRepr in pmaj.
    rewrite CReal_red_seq in pmaj.
    destruct (Z_ge_lt_dec 0 p) as [Hdec|Hdec].
    + (* The usual case that p<=0 and 2^p is small *)
      (* In this case the conversion of Z to nat and back is id *)
      unfold CReal_of_DReal_seq in pmaj.
      destruct (DRealQlimExp2 (DRealAbstr x) (Z.to_nat (- p))) as [q [Hql Hqr]].
      unfold proj1_sig in pmaj.
      pose proof (DRealAbstrFalse x _ (Z.to_nat (- p)) Hqr) as Hq; clear Hql Hqr.
      rewrite <- Qpower_2_neg_eq_natpow_inv in Hq.
      rewrite Z2Nat.id, Z.opp_involutive in Hq by lia; clear Hdec.
      lra.
    + (* The case that p>0 and 2^p is large *)
      (* In this case we use CReal_of_DReal_seq_max_prec_1 to rewrite the index to 0 *)
      rewrite CReal_of_DReal_seq_max_prec_1 in pmaj by lia.
      unfold CReal_of_DReal_seq in pmaj.
      change (Z.to_nat (-0))%Z with 0%nat in pmaj.
      destruct (DRealQlimExp2 (DRealAbstr x) 0) as [q [Hql Hqr]].
      unfold proj1_sig in pmaj.
      pose proof (DRealAbstrFalse'' x _ p%nat Hqr) as Hq; clear Hql Hqr.
      rewrite <- Qpower_2_neg_eq_natpow_inv in Hq.
      change (- Z.of_nat 0)%Z with 0%Z in Hq.
      pose proof (Qpower_le_compat_l 2 1 p ltac:(lia) ltac:(lra)) as Hpowle.
      change (2^1)%Q with 2%Q in Hpowle.
      lra.
  - intros [p pmaj].
    unfold DRealRepr in pmaj.
    rewrite CReal_red_seq in pmaj.
    unfold CReal_of_DReal_seq in pmaj.
    destruct (DRealQlimExp2 (DRealAbstr x) (Z.to_nat (- p))) as [q [Hql Hqr]].
    unfold proj1_sig in pmaj.
    unfold DRealAbstr, proj1_sig in Hql.
    match type of Hql with context [ if ?a then _ else _ ] => destruct a as [H'|H']end.
      2: discriminate. clear Hql Hqr.
    destruct H' as [n nmaj]. apply nmaj; clear nmaj.
    apply (Qplus_lt_l _ _ (seq x p + 2 ^ (- Z.of_nat n))) in pmaj.
   ring_simplify in pmaj. apply Qlt_le_weak. rewrite Qplus_comm.
    apply (Qlt_trans _ ((2 * 2^p) + seq x p + (2 ^ (- Z.of_nat n)))).
    2: exact pmaj. clear pmaj.
    apply (Qplus_lt_l _ _ (-seq x p)).
    apply (Qle_lt_trans _ _ _ (Qle_Qabs _)).
    destruct (Z_le_gt_dec p (- Z.of_nat n)).
    + apply (Qlt_trans _ (2 ^ (- Z.of_nat n))).
      1: apply (cauchy x).
      1, 2: lia.
      pose proof Qpower_0_lt 2 p; lra.
    + apply (Qlt_trans _ (2^p)).
      1: apply (cauchy x).
      1, 2: lia.
      pose proof Qpower_0_lt 2 (- Z.of_nat n).
      pose proof Qpower_0_lt 2 p.
      lra.
Qed.
