(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.HLevels.
Require Import QArith.
Require Import Qabs.
Require Import ConstructiveCauchyReals.
Require Import ConstructiveRcomplete.

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
    left. reflexivity. right. discriminate.
    right. discriminate. left. reflexivity.
  - apply forall_hprop. intro q. apply impl_hprop. apply not_hprop.
Qed.

Lemma lowerCutBelow : forall f : Q -> bool,
    isLowerCut f -> { q : Q | f q = true }.
Proof.
  intros.
  destruct (sig_forall_dec (fun n:nat => f (-(Z.of_nat n # 1))%Q = false)).
  - intro n. destruct (f (-(Z.of_nat n # 1))%Q).
    right. discriminate. left. reflexivity.
  - destruct s. exists (-(Z.of_nat x # 1))%Q.
    destruct (f (-(Z.of_nat x # 1))%Q).
    reflexivity. exfalso. apply n. reflexivity.
  - exfalso. destruct H, H0, H1. apply H1. intro q.
    destruct (f q) eqn:des. 2: reflexivity. exfalso.
    destruct (Qarchimedean (-q)) as [p pmaj].
    rewrite <- (Qplus_lt_l _ _ (q-(Z.pos p # 1))) in pmaj.
    ring_simplify in pmaj.
    specialize (H (- (Z.pos p#1))%Q q).
    specialize (e (Pos.to_nat p)).
    rewrite positive_nat_Z in e. rewrite H in e. discriminate.
    2: exact des. ring_simplify. apply Qlt_le_weak, pmaj.
Qed.

Lemma lowerCutAbove : forall f : Q -> bool,
    isLowerCut f -> { q : Q | f q = false }.
Proof.
  intros.
  destruct (sig_forall_dec (fun n => f (Z.of_nat n # 1)%Q = true)).
  - intro n. destruct (f (Z.of_nat n # 1)%Q).
    left. reflexivity. right. discriminate.
  - destruct s. exists (Z.of_nat x # 1)%Q. destruct (f (Z.of_nat x # 1)%Q).
    exfalso. apply n. reflexivity. reflexivity.
  - exfalso. destruct H, H0, H1. apply H0. intro q.
    destruct (Qarchimedean q) as [p pmaj].
    apply (H q (Z.of_nat (Pos.to_nat p) # 1)%Q).
    rewrite positive_nat_Z. apply Qlt_le_weak, pmaj. apply e.
Qed.

Definition DReal : Set
  := { f : Q -> bool | isLowerCut f }.

Fixpoint DRealQlim_rec (f : Q -> bool) (low : isLowerCut f) (n p : nat) { struct p }
  : f (proj1_sig (lowerCutBelow f low) + (Z.of_nat p # Pos.of_nat (S n)))%Q = false
    -> { q : Q | f q = true /\ f (q + (1 # Pos.of_nat (S n)))%Q = false }.
Proof.
  intros. destruct p.
  - exfalso. destruct (lowerCutBelow f low); unfold proj1_sig in H.
    destruct low. rewrite (H0 _ x) in H. discriminate. simpl.
    apply (Qplus_le_l _ _ (-x)). ring_simplify. discriminate. exact e.
  - destruct (f (proj1_sig (lowerCutBelow f low) + (Z.of_nat p # Pos.of_nat (S n)))%Q) eqn:des.
    + exists (proj1_sig (lowerCutBelow f low) + (Z.of_nat p # Pos.of_nat (S n)))%Q.
      split. exact des.
      destruct (f (proj1_sig (lowerCutBelow f low)
                   + (Z.of_nat p # Pos.of_nat (S n)) + (1 # Pos.of_nat (S n)))%Q) eqn:d.
      2: reflexivity. exfalso.
      destruct low.
      rewrite (e _ (proj1_sig (lowerCutBelow f (conj e a)) + (Z.of_nat p # Pos.of_nat (S n)) + (1 # Pos.of_nat (S n))))%Q in H.
      discriminate. 2: exact d. rewrite <- Qplus_assoc, Qplus_le_r.
      rewrite Qinv_plus_distr.
      replace (Z.of_nat p + 1)%Z with (Z.of_nat (S p))%Z. apply Qle_refl.
      replace 1%Z with (Z.of_nat 1). rewrite <- (Nat2Z.inj_add p 1).
      apply f_equal. rewrite Nat.add_comm. reflexivity. reflexivity.
    + destruct (DRealQlim_rec f low n p des) as [q qmaj].
      exists q. exact qmaj.
Qed.

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
  discriminate. 2: exact des.
  setoid_replace (Z.of_nat (S n * Pos.to_nat p) # Pos.of_nat (S n))%Q with (Z.pos p # 1)%Q.
  apply (Qplus_lt_l _ _ x0) in pmaj. ring_simplify in pmaj.
  apply Qlt_le_weak, pmaj. rewrite Nat2Z.inj_mul, positive_nat_Z.
  unfold Qeq, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_comm.
  replace (Z.of_nat (S n)) with (Z.pos (Pos.of_nat (S n))). reflexivity.
  simpl. destruct n. reflexivity. apply f_equal.
  apply Pos.succ_of_nat. discriminate.
Qed.

Definition DRealAbstr : CReal -> DReal.
Proof.
  intro x.
  assert (forall (q : Q) (n : nat),
   {(fun n0 : nat => (proj1_sig x (S n0) <= q + (1 # Pos.of_nat (S n0)))%Q) n} +
   {~ (fun n0 : nat => (proj1_sig x (S n0) <= q + (1 # Pos.of_nat (S n0)))%Q) n}).
  { intros. destruct (Qlt_le_dec (q + (1 # Pos.of_nat (S n))) (proj1_sig x (S n))).
    right. apply (Qlt_not_le _ _ q0). left. exact q0. }

  exists (fun q:Q => if sig_forall_dec (fun n:nat => Qle (proj1_sig x (S n)) (q + (1#Pos.of_nat (S n)))) (H q)
             then true else false).
  repeat split.
  - intros.
    destruct (sig_forall_dec (fun n : nat => (proj1_sig x (S n) <= q + (1 # Pos.of_nat (S n)))%Q)
                             (H q)).
    reflexivity. exfalso.
    destruct (sig_forall_dec (fun n : nat => (proj1_sig x (S n) <= r + (1 # Pos.of_nat (S n)))%Q)
                             (H r)).
    destruct s. apply n.
    apply (Qle_trans _ _ _ (q0 x0)).
    apply Qplus_le_l. exact H0. discriminate.
  - intro abs. destruct (Rfloor x) as [z [_ zmaj]].
    specialize (abs (z+3 # 1)%Q).
    destruct (sig_forall_dec (fun n : nat => (proj1_sig x (S n) <= (z+3 # 1) + (1 # Pos.of_nat (S n)))%Q)
                             (H (z+3 # 1)%Q)).
    2: exfalso; discriminate. clear abs. destruct s as [n nmaj]. apply nmaj.
    rewrite <- (inject_Q_plus (z#1) 2) in zmaj.
    apply CRealLt_asym in zmaj. rewrite <- CRealLe_not_lt in zmaj.
    specialize (zmaj (Pos.of_nat (S n))). unfold inject_Q, proj1_sig in zmaj.
    rewrite Nat2Pos.id in zmaj. 2: discriminate.
    destruct x as [xn xcau]; unfold proj1_sig.
    rewrite Qinv_plus_distr in zmaj.
    apply (Qplus_le_l _ _ (-(z + 2 # 1))). apply (Qle_trans _ _ _ zmaj).
    apply (Qplus_le_l _ _ (-(1 # Pos.of_nat (S n)))). apply (Qle_trans _ 1).
    unfold Qopp, Qnum, Qden. rewrite Qinv_plus_distr.
    unfold Qle, Qnum, Qden. apply Z2Nat.inj_le. discriminate. discriminate.
    do 2 rewrite Z.mul_1_l. unfold Z.to_nat. rewrite Nat2Pos.id. 2: discriminate.
    apply le_n_S, le_0_n. setoid_replace (- (z + 2 # 1))%Q with (-(z+2) #1)%Q.
    2: reflexivity. ring_simplify. rewrite Qinv_plus_distr.
    replace (z + 3 + - (z + 2))%Z with 1%Z. apply Qle_refl. ring.
  - intro abs. destruct (Rfloor x) as [z [zmaj _]].
    specialize (abs (z-4 # 1)%Q).
    destruct (sig_forall_dec (fun n : nat => (proj1_sig x (S n) <= (z-4 # 1) + (1 # Pos.of_nat (S n)))%Q)
                             (H (z-4 # 1)%Q)).
    exfalso; discriminate. clear abs.
    apply CRealLt_asym in zmaj. apply zmaj. clear zmaj.
    exists 1%positive. unfold inject_Q, proj1_sig.
    specialize (q O).
    destruct x as [xn xcau]; unfold proj1_sig; unfold proj1_sig in q.
    unfold Pos.of_nat in q. rewrite Qinv_plus_distr in q.
    unfold Pos.to_nat; simpl. apply (Qplus_lt_l _ _ (xn 1%nat - 2)).
    ring_simplify. rewrite Qinv_plus_distr.
    apply (Qle_lt_trans _ _ _ q). apply Qlt_minus_iff.
    unfold Qopp, Qnum, Qden. rewrite Qinv_plus_distr.
    replace (z + -2 + - (z - 4 + 1))%Z with 1%Z. 2: ring. reflexivity.
  - intros q H0 abs.
    destruct (sig_forall_dec (fun n : nat => (proj1_sig x (S n) <= q + (1 # Pos.of_nat (S n)))%Q) (H q)).
    2: exfalso; discriminate. clear H0.
    destruct x as [xn xcau]; unfold proj1_sig in abs, s.
    destruct s as [n nmaj].
    (* We have that q < x as real numbers. The middle
       (q + xSn - 1/Sn)/2 is also lower than x, witnessed by the same index n. *)
    specialize (abs ((q + xn (S n) - (1 # Pos.of_nat (S n))%Q)/2)%Q).
    destruct abs.
    + apply (Qmult_le_r _ _ 2) in H0. field_simplify in H0.
      apply (Qplus_le_r _ _ ((1 # Pos.of_nat (S n)) - q)) in H0.
      ring_simplify in H0. apply nmaj. rewrite Qplus_comm. exact H0. reflexivity.
    + destruct (sig_forall_dec
           (fun n0 : nat =>
            (xn (S n0) <= (q + xn (S n) - (1 # Pos.of_nat (S n))) / 2 + (1 # Pos.of_nat (S n0)))%Q)
           (H ((q + xn (S n) - (1 # Pos.of_nat (S n))) / 2)%Q)).
      discriminate. clear H0. specialize (q0 n).
      apply (Qmult_le_l _ _ 2) in q0. field_simplify in q0.
      apply (Qplus_le_l _ _ (-xn (S n))) in q0. ring_simplify in q0.
      contradiction. reflexivity.
Defined.

Lemma UpperAboveLower : forall (f : Q -> bool) (q r : Q),
    isLowerCut f
    -> f q = true
    -> f r = false
    -> Qlt q r.
Proof.
  intros. destruct H. apply Qnot_le_lt. intro abs.
  rewrite (H r q abs) in H1. discriminate. exact H0.
Qed.

Definition DRealRepr : DReal -> CReal.
Proof.
  intro x. exists (fun n => proj1_sig (DRealQlim x n)).
  intros n p q H H0.
  destruct (DRealQlim x p), (DRealQlim x q); unfold proj1_sig.
  destruct x as [f low]; unfold proj1_sig in a0, a.
  apply Qabs_case.
  - intros. apply (Qlt_le_trans _ (1 # Pos.of_nat (S q))).
    apply (Qplus_lt_l _ _ x1). ring_simplify. apply (UpperAboveLower f).
    exact low. apply a. apply a0. unfold Qle, Qnum, Qden.
    do 2 rewrite Z.mul_1_l. apply Pos2Z.pos_le_pos.
    apply Pos2Nat.inj_le. rewrite Nat2Pos.id. apply (le_trans _ _ _ H0), le_S, le_refl.
    discriminate.
  - intros. apply (Qlt_le_trans _ (1 # Pos.of_nat (S p))).
    apply (Qplus_lt_l _ _ x0). ring_simplify. apply (UpperAboveLower f).
    exact low. apply a0. apply a. unfold Qle, Qnum, Qden.
    do 2 rewrite Z.mul_1_l. apply Pos2Z.pos_le_pos.
    apply Pos2Nat.inj_le. rewrite Nat2Pos.id. apply (le_trans _ _ _ H), le_S, le_refl.
    discriminate.
Defined.

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
    destruct (f q), (g q). reflexivity.
    exfalso. specialize (H (eq_refl _)). discriminate.
    exfalso. specialize (H0 (eq_refl _)). discriminate.
    reflexivity. }
  subst g. replace cg with cf. reflexivity.
  apply isLowerCut_hprop.
Qed.

Lemma lowerUpper : forall (f : Q -> bool) (q r : Q),
    isLowerCut f -> Qle q r -> f q = false -> f r = false.
Proof.
  intros. destruct H. specialize (H q r H0). destruct (f r) eqn:desR.
  2: reflexivity. exfalso. specialize (H (eq_refl _)).
  rewrite H in H1. discriminate.
Qed.

Lemma DRealOpen : forall (x : DReal) (q : Q),
    proj1_sig x q = true
    -> { r : Q | Qlt q r /\ proj1_sig x r = true }.
Proof.
  intros.
  destruct (sig_forall_dec (fun n => Qle (proj1_sig (DRealQlim x n)) q)).
  - intro n. destruct (DRealQlim x n); unfold proj1_sig.
    destruct (Qlt_le_dec q x0). right. exact (Qlt_not_le _ _ q0).
    left. exact q0.
  - destruct s. apply Qnot_le_lt in n.
    destruct (DRealQlim x x0); unfold proj1_sig in n.
    exists x1. split. exact n. apply a.
  - exfalso. destruct x as [f low]. unfold proj1_sig in H, q0.
    destruct low, a, a. apply (n1 q H). intros.
    destruct (Qlt_le_dec q r). 2: left; exact q1. right.
    destruct (Qarchimedean (/(r - q))) as [p pmaj].
    specialize (q0 (Pos.to_nat p)).
    destruct (DRealQlim (exist _ f (conj e (conj n (conj n0 n1)))) (Pos.to_nat p))
      as [s smaj].
    unfold proj1_sig in smaj.
    apply (lowerUpper f (s + (1 # Pos.of_nat (S (Pos.to_nat p))))).
    exact (conj e (conj n (conj n0 n1))).
    2: apply smaj. apply (Qle_trans _ (s + (r-q))).
    apply Qplus_le_r. apply (Qle_trans _ (1 # p)).
    unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_l.
    apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
    rewrite Nat2Pos.id. apply le_S, le_refl. discriminate.
    apply (Qmult_le_l _ _ ( (Z.pos p # 1) / (r-q))).
    rewrite <- (Qmult_0_r (Z.pos p #1)). apply Qmult_lt_l.
    reflexivity. apply Qinv_lt_0_compat.
    unfold Qminus. rewrite <- Qlt_minus_iff. exact q1.
    unfold Qdiv. rewrite Qmult_comm, <- Qmult_assoc.
    rewrite (Qmult_comm (/(r-q))), Qmult_inv_r, Qmult_assoc.
    setoid_replace ((1 # p) * (Z.pos p # 1))%Q with 1%Q.
    2: reflexivity. rewrite Qmult_1_l, Qmult_1_r.
    apply Qlt_le_weak, pmaj. intro abs. apply Qlt_minus_iff in q1.
    rewrite abs in q1. apply (Qlt_not_le _ _ q1), Qle_refl.
    apply (Qplus_le_l _ _ (q-r)). ring_simplify. exact q0.
Qed.

Lemma DRealReprQ : forall (x : DReal) (q : Q),
    proj1_sig x q = true
    -> CRealLt (inject_Q q) (DRealRepr x).
Proof.
  intros.
  destruct (DRealOpen x q H) as [r rmaj].
  destruct (Qarchimedean (4/(r - q))) as [p pmaj].
  exists p.
  destruct x as [f low]; unfold DRealRepr, inject_Q, proj1_sig.
  destruct (DRealQlim (exist _ f low) (Pos.to_nat p)) as [s smaj].
  unfold proj1_sig in smaj, rmaj.
  apply (Qplus_lt_l _ _ (q+ (1 # Pos.of_nat (S (Pos.to_nat p))))).
  ring_simplify. rewrite <- (Qplus_comm s).
  apply (UpperAboveLower f _ _ low). 2: apply smaj.
  destruct low. apply (e _ r). 2: apply rmaj.
  rewrite <- (Qplus_comm q).
  apply (Qle_trans _ (q + (4#p))).
  - rewrite <- Qplus_assoc. apply Qplus_le_r.
    apply (Qle_trans _ ((2#p) + (1#p))).
    apply Qplus_le_r.
    unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_l.
    apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
    rewrite Nat2Pos.id. apply le_S, le_refl. discriminate.
    rewrite Qinv_plus_distr. unfold Qle, Qnum, Qden.
    apply Z.mul_le_mono_nonneg_r. discriminate. discriminate.
  - apply (Qle_trans _ (q + (r-q))). 2: ring_simplify; apply Qle_refl.
    apply Qplus_le_r.
    apply (Qmult_le_l _ _ ( (Z.pos p # 1) / (r-q))).
    rewrite <- (Qmult_0_r (Z.pos p #1)). apply Qmult_lt_l.
    reflexivity. apply Qinv_lt_0_compat.
    unfold Qminus. rewrite <- Qlt_minus_iff. apply rmaj.
    unfold Qdiv. rewrite Qmult_comm, <- Qmult_assoc.
    rewrite (Qmult_comm (/(r-q))), Qmult_inv_r, Qmult_assoc.
    setoid_replace ((4 # p) * (Z.pos p # 1))%Q with 4%Q.
    2: reflexivity. rewrite Qmult_1_r.
    apply Qlt_le_weak, pmaj. intro abs. destruct rmaj.
    apply Qlt_minus_iff in H0.
    rewrite abs in H0. apply (Qlt_not_le _ _ H0), Qle_refl.
Qed.

Lemma DRealReprQup : forall (x : DReal) (q : Q),
    proj1_sig x q = false
    -> CRealLe (DRealRepr x) (inject_Q q).
Proof.
  intros x q H [p pmaj].
  unfold inject_Q, DRealRepr, proj1_sig in pmaj.
  destruct (DRealQlim x (Pos.to_nat p)) as [r rmaj], rmaj.
  clear H1. destruct x as [f low], low; unfold proj1_sig in H, H0.
  apply (Qplus_lt_l _ _ q) in pmaj. ring_simplify in pmaj.
  rewrite (e _ r) in H. discriminate. 2: exact H0.
  apply Qlt_le_weak. apply (Qlt_trans _ ((2#p)+q)). 2: exact pmaj.
  apply (Qplus_lt_l _ _ (-q)). ring_simplify. reflexivity.
Qed.

Lemma DRealQuot1 : forall x y:DReal, CRealEq (DRealRepr x) (DRealRepr y) -> x = y.
Proof.
  intros. destruct H. apply Rle_antisym.
  - clear H. intros q H1. destruct (proj1_sig y q) eqn:des.
    reflexivity. exfalso. apply H0.
    apply (CReal_le_lt_trans _ (inject_Q q)). apply DRealReprQup.
    exact des. apply DRealReprQ. exact H1.
  - clear H0. intros q H1. destruct (proj1_sig x q) eqn:des.
    reflexivity. exfalso. apply H.
    apply (CReal_le_lt_trans _ (inject_Q q)). apply DRealReprQup.
    exact des. apply DRealReprQ. exact H1.
Qed.

Lemma DRealAbstrFalse : forall (x : CReal) (q : Q) (n : nat),
    proj1_sig (DRealAbstr x) q = false
    -> (proj1_sig x (S n) <= q + (1 # Pos.of_nat (S n)))%Q.
Proof.
  intros. destruct x as [xn xcau].
  unfold DRealAbstr, proj1_sig in H.
  destruct (
        sig_forall_dec (fun n : nat => (xn (S n) <= q + (1 # Pos.of_nat (S n)))%Q)
          (fun n : nat =>
           match Qlt_le_dec (q + (1 # Pos.of_nat (S n))) (xn (S n)) with
           | left q0 => right (Qlt_not_le (q + (1 # Pos.of_nat (S n))) (xn (S n)) q0)
           | right q0 => left q0
           end)).
  discriminate. apply q0.
Qed.

Lemma DRealQuot2 : forall x:CReal, CRealEq (DRealRepr (DRealAbstr x)) x.
Proof.
  split.
  - intros [p pmaj]. unfold DRealRepr, proj1_sig in pmaj.
    destruct x as [xn xcau].
    destruct (DRealQlim (DRealAbstr (exist _ xn xcau)) (Pos.to_nat p))
      as [q [_ qmaj]].
    (* By pmaj, q + 1/p < x as real numbers.
       But by qmaj x <= q + 1/(p+1), contradiction. *)
    apply (DRealAbstrFalse _ _ (pred (Pos.to_nat p))) in qmaj.
    unfold proj1_sig in qmaj.
    rewrite Nat.succ_pred in qmaj.
    apply (Qlt_not_le _ _ pmaj), (Qplus_le_l _ _ q).
    ring_simplify. apply (Qle_trans _ _ _ qmaj).
    rewrite <- Qplus_assoc. apply Qplus_le_r.
    rewrite Pos2Nat.id. apply (Qle_trans _ ((1#p)+(1#p))).
    apply Qplus_le_l. unfold Qle, Qnum, Qden.
    do 2 rewrite Z.mul_1_l.
    apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
    rewrite Nat2Pos.id. apply le_S, le_refl. discriminate.
    rewrite Qinv_plus_distr. apply Qle_refl.
    intro abs. pose proof (Pos2Nat.is_pos p).
    rewrite abs in H. inversion H.
  - intros [p pmaj]. unfold DRealRepr, proj1_sig in pmaj.
    destruct x as [xn xcau].
    destruct (DRealQlim (DRealAbstr (exist _ xn xcau)) (Pos.to_nat p))
      as [q [qmaj _]].
    (* By pmaj, x < q - 1/p *)
    unfold DRealAbstr, proj1_sig in qmaj.
    destruct (
           sig_forall_dec (fun n : nat => (xn (S n) <= q + (1 # Pos.of_nat (S n)))%Q)
             (fun n : nat =>
              match Qlt_le_dec (q + (1 # Pos.of_nat (S n))) (xn (S n)) with
              | left q0 =>
                  right (Qlt_not_le (q + (1 # Pos.of_nat (S n))) (xn (S n)) q0)
              | right q0 => left q0
              end)).
    2: discriminate. clear qmaj.
    destruct s as [n nmaj]. apply nmaj.
    apply (Qplus_lt_l _ _ (xn (Pos.to_nat p) + (1#Pos.of_nat (S n)))) in pmaj.
    ring_simplify in pmaj. apply Qlt_le_weak. rewrite Qplus_comm.
    apply (Qlt_trans _ ((2 # p) + xn (Pos.to_nat p) + (1 # Pos.of_nat (S n)))).
    2: exact pmaj.
    apply (Qplus_lt_l _ _ (-xn (Pos.to_nat p))).
    apply (Qle_lt_trans _ _ _ (Qle_Qabs _)).
    destruct (le_lt_dec (S n) (Pos.to_nat p)).
    + specialize (xcau (Pos.of_nat (S n)) (S n) (Pos.to_nat p)).
      apply (Qlt_trans _ (1# Pos.of_nat (S n))). apply xcau.
      rewrite Nat2Pos.id. apply le_refl. discriminate.
      rewrite Nat2Pos.id. exact l. discriminate.
      apply (Qplus_lt_l _ _ (-(1#Pos.of_nat (S n)))).
      ring_simplify. reflexivity.
    + apply (Qlt_trans _ (1#p)). apply xcau.
      apply le_S_n in l. apply le_S, l. apply le_refl.
      ring_simplify. apply (Qlt_trans _ (2#p)).
      unfold Qlt, Qnum, Qden.
      apply Z.mul_lt_mono_pos_r. reflexivity. reflexivity.
      apply (Qplus_lt_l _ _ (-(2#p))). ring_simplify. reflexivity.
Qed.
