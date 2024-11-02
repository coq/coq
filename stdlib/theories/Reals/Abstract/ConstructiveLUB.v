(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(************************************************************************)

(** Proof that LPO and the excluded middle for negations imply
    the existence of least upper bounds for all non-empty and bounded
    subsets of the real numbers.

   WARNING: this file is experimental and likely to change in future releases.
*)

Require Import Znat QArith_base Qabs.
Require Import ConstructiveReals.
Require Import ConstructiveAbs.
Require Import ConstructiveLimits.
Require Import Logic.ConstructiveEpsilon.

Local Open Scope ConstructiveReals.

Definition sig_forall_dec_T : Type
  := forall (P : nat -> Prop), (forall n, {P n} + {~P n})
                   -> {n | ~P n} + {forall n, P n}.

Definition sig_not_dec_T : Type := forall P : Prop, { ~~P } + { ~P }.

Definition is_upper_bound {R : ConstructiveReals}
           (E:CRcarrier R -> Prop) (m:CRcarrier R)
  := forall x:CRcarrier R, E x -> x <= m.

Definition is_lub {R : ConstructiveReals}
           (E:CRcarrier R -> Prop) (m:CRcarrier R) :=
  is_upper_bound E m /\ (forall b:CRcarrier R, is_upper_bound E b -> m <= b).

Lemma CRlt_lpo_dec : forall {R : ConstructiveReals} (x y : CRcarrier R),
    (forall (P : nat -> Prop), (forall n, {P n} + {~P n})
                    -> {n | ~P n} + {forall n, P n})
    -> sum (x < y) (y <= x).
Proof.
  intros R x y lpo.
  assert (forall (z:CRcarrier R) (n : nat), z < z + CR_of_Q R (1 # Pos.of_nat (S n))).
  { intros. apply (CRle_lt_trans _ (z+0)).
    - rewrite CRplus_0_r. apply CRle_refl.
    - apply CRplus_lt_compat_l.
      apply CR_of_Q_pos. reflexivity. }
  pose (fun n:nat => let (q,_) := CR_Q_dense
                               R x (x + CR_of_Q R (1 # Pos.of_nat (S n))) (H x n)
                in q)
    as xn.
  pose (fun n:nat => let (q,_) := CR_Q_dense
                               R y (y + CR_of_Q R (1 # Pos.of_nat (S n))) (H y n)
                in q)
    as yn.
  destruct (lpo (fun n => Qle (yn n) (xn n + (1 # Pos.of_nat (S n))))).
  - intro n. destruct (Q_dec (yn n) (xn n + (1 # Pos.of_nat (S n)))).
    + destruct s.
      * left. apply Qlt_le_weak, q.
      * right. apply (Qlt_not_le _ _ q).
    + left.
      rewrite q. apply Qle_refl.
  - left. destruct s as [n nmaj]. apply Qnot_le_lt in nmaj.
    apply (CRlt_le_trans _ (CR_of_Q R (xn n))).
    + unfold xn.
      destruct (CR_Q_dense R x (x + CR_of_Q R (1 # Pos.of_nat (S n))) (H x n)).
      exact (fst p).
    + apply (CRle_trans _ (CR_of_Q R (yn n - (1 # Pos.of_nat (S n))))).
      * apply CR_of_Q_le. rewrite <- (Qplus_le_l _ _ (1# Pos.of_nat (S n))).
        ring_simplify. apply Qlt_le_weak, nmaj.
      * unfold yn.
        destruct (CR_Q_dense R y (y + CR_of_Q R (1 # Pos.of_nat (S n))) (H y n)).
        unfold Qminus. rewrite CR_of_Q_plus, CR_of_Q_opp.
        apply (CRplus_le_reg_r (CR_of_Q R (1 # Pos.of_nat (S n)))).
        rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
        apply CRlt_asym, (snd p).
  - right. apply (CR_cv_le (fun n => CR_of_Q R (yn n))
                           (fun n => CR_of_Q R (xn n) + CR_of_Q R (1 # Pos.of_nat (S n)))).
    + intro n. rewrite <- CR_of_Q_plus. apply CR_of_Q_le. exact (q n).
    + intro p. exists (Pos.to_nat p). intros.
      unfold yn.
      destruct (CR_Q_dense R y (y + CR_of_Q R (1 # Pos.of_nat (S i))) (H y i)).
      rewrite CRabs_right.
      * apply (CRplus_le_reg_r y).
        unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
        rewrite CRplus_comm.
        apply (CRle_trans _ (y + CR_of_Q R (1 # Pos.of_nat (S i)))).
        -- apply CRlt_asym, (snd p0).
        -- apply CRplus_le_compat_l.
           apply CR_of_Q_le. unfold Qle, Qnum, Qden.
           rewrite Z.mul_1_l, Z.mul_1_l. apply Pos2Z.pos_le_pos.
           apply Pos2Nat.inj_le. rewrite Nat2Pos.id.
           ++ apply le_S, H0.
           ++ discriminate.
      * rewrite <- (CRplus_opp_r y).
        apply CRplus_le_compat_r, CRlt_asym, p0.
    + apply (CR_cv_proper _ (x+0)). 2: rewrite CRplus_0_r; reflexivity.
      apply CR_cv_plus.
      * intro p. exists (Pos.to_nat p). intros.
        unfold xn.
        destruct (CR_Q_dense R x (x + CR_of_Q R (1 # Pos.of_nat (S i))) (H x i)).
        rewrite CRabs_right.
        -- apply (CRplus_le_reg_r x).
           unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
           rewrite CRplus_comm.
           apply (CRle_trans _ (x + CR_of_Q R (1 # Pos.of_nat (S i)))).
           ++ apply CRlt_asym, (snd p0).
           ++ apply CRplus_le_compat_l.
              apply CR_of_Q_le. unfold Qle, Qnum, Qden.
              rewrite Z.mul_1_l, Z.mul_1_l. apply Pos2Z.pos_le_pos.
              apply Pos2Nat.inj_le. rewrite Nat2Pos.id.
              ** apply le_S, H0.
              ** discriminate.
        -- rewrite <- (CRplus_opp_r x).
           apply CRplus_le_compat_r, CRlt_asym, p0.
      * intro p. exists (Pos.to_nat p). intros.
        unfold CRminus. rewrite CRopp_0, CRplus_0_r, CRabs_right.
        -- apply CR_of_Q_le. unfold Qle, Qnum, Qden.
           rewrite Z.mul_1_l, Z.mul_1_l. apply Pos2Z.pos_le_pos.
           apply Pos2Nat.inj_le. rewrite Nat2Pos.id.
           ++ apply le_S, H0.
           ++ discriminate.
        -- apply CR_of_Q_le. discriminate.
Qed.

Lemma is_upper_bound_dec :
  forall {R : ConstructiveReals} (E:CRcarrier R -> Prop) (x:CRcarrier R),
    sig_forall_dec_T
    -> sig_not_dec_T
    -> { is_upper_bound E x } + { ~is_upper_bound E x }.
Proof.
  intros R E x lpo sig_not_dec.
  destruct (sig_not_dec (~exists y:CRcarrier R, E y /\ CRltProp R x y)).
  - left. intros y H.
    destruct (CRlt_lpo_dec x y lpo). 2: exact c.
    exfalso. apply n. intro abs. apply abs. clear abs.
    exists y. split.
    + exact H.
    + apply CRltForget. exact c.
  - right. intro abs. apply n. intros [y [H H0]].
    specialize (abs y H). apply CRltEpsilon in H0. contradiction.
Qed.

Lemma is_upper_bound_epsilon :
  forall {R : ConstructiveReals} (E:CRcarrier R -> Prop),
    sig_forall_dec_T
    -> sig_not_dec_T
    -> (exists x:CRcarrier R, is_upper_bound E x)
    -> { n:nat | is_upper_bound E (CR_of_Q R (Z.of_nat n # 1)) }.
Proof.
  intros R E lpo sig_not_dec Ebound.
  apply constructive_indefinite_ground_description_nat.
  - intro n. apply is_upper_bound_dec.
    + exact lpo.
    + exact sig_not_dec.
  - destruct Ebound as [x H]. destruct (CRup_nat x) as [n nmaj]. exists n.
    intros y ey. specialize (H y ey).
    apply (CRle_trans _ x _ H). apply CRlt_asym, nmaj.
Qed.

Lemma is_upper_bound_not_epsilon :
  forall {R : ConstructiveReals} (E:CRcarrier R -> Prop),
    sig_forall_dec_T
    -> sig_not_dec_T
    -> (exists x : CRcarrier R, E x)
    -> { m:nat | ~is_upper_bound E (-CR_of_Q R (Z.of_nat m # 1)) }.
Proof.
  intros R E lpo sig_not_dec H.
  apply constructive_indefinite_ground_description_nat.
  - intro n.
    destruct (is_upper_bound_dec E (-CR_of_Q R (Z.of_nat n # 1)) lpo sig_not_dec).
    + right. intro abs. contradiction.
    + left. exact n0.
  - destruct H as [x H]. destruct (CRup_nat (-x)) as [n H0].
    exists n. intro abs. specialize (abs x H).
    apply abs. rewrite <- (CRopp_involutive x).
    apply CRopp_gt_lt_contravar. exact H0.
Qed.

(* Decidable Dedekind cuts are Cauchy reals. *)
Record DedekindDecCut : Type :=
  {
    DDupcut : Q -> Prop;
    DDproper : forall q r : Q, (q == r -> DDupcut q -> DDupcut r)%Q;
    DDlow : Q;
    DDhigh : Q;
    DDdec : forall q:Q, { DDupcut q } + { ~DDupcut q };
    DDinterval : forall q r : Q, Qle q r -> DDupcut q -> DDupcut r;
    DDhighProp : DDupcut DDhigh;
    DDlowProp : ~DDupcut DDlow;
  }.

Lemma DDlow_below_up : forall (upcut : DedekindDecCut) (a b : Q),
    DDupcut upcut a -> ~DDupcut upcut b -> Qlt b a.
Proof.
  intros. destruct (Qlt_le_dec b a).
  - exact q.
  - exfalso. apply H0. apply (DDinterval upcut a).
    + exact q.
    + exact H.
Qed.

Fixpoint DDcut_limit_fix (upcut : DedekindDecCut) (r : Q) (n : nat) :
  Qlt 0 r
  -> (DDupcut upcut (DDlow upcut + (Z.of_nat n#1) * r))
  -> { q : Q | DDupcut upcut q /\ ~DDupcut upcut (q - r) }.
Proof.
  destruct n.
  - intros. exfalso. simpl in H0.
    apply (DDproper upcut _ (DDlow upcut)) in H0. 2: ring.
    exact (DDlowProp upcut H0).
  - intros. destruct (DDdec upcut (DDlow upcut + (Z.of_nat n # 1) * r)).
    + exact (DDcut_limit_fix upcut r n H d).
    + exists (DDlow upcut + (Z.of_nat (S n) # 1) * r)%Q. split.
      * exact H0.
      * intro abs.
        apply (DDproper upcut _ (DDlow upcut + (Z.of_nat n # 1) * r)) in abs.
        -- contradiction.
        -- rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite <- Qinv_plus_distr.
           ring.
Qed.

Lemma DDcut_limit : forall (upcut : DedekindDecCut) (r : Q),
  Qlt 0 r
  -> { q : Q | DDupcut upcut q /\ ~DDupcut upcut (q - r) }.
Proof.
  intros.
  destruct (Qarchimedean ((DDhigh upcut - DDlow upcut)/r)) as [n nmaj].
  apply (DDcut_limit_fix upcut r (Pos.to_nat n) H).
  apply (Qmult_lt_r _ _ r) in nmaj. 2: exact H.
  unfold Qdiv in nmaj.
  rewrite <- Qmult_assoc, (Qmult_comm (/r)), Qmult_inv_r, Qmult_1_r in nmaj.
  - apply (DDinterval upcut (DDhigh upcut)). 2: exact (DDhighProp upcut).
    apply Qlt_le_weak. apply (Qplus_lt_r _ _ (-DDlow upcut)).
    rewrite Qplus_assoc, <- (Qplus_comm (DDlow upcut)), Qplus_opp_r,
      Qplus_0_l, Qplus_comm.
    rewrite positive_nat_Z. exact nmaj.
  - intros abs. rewrite abs in H. exact (Qlt_irrefl 0 H).
Qed.

Lemma glb_dec_Q : forall {R : ConstructiveReals} (upcut : DedekindDecCut),
    { x : CRcarrier R
    | forall r:Q, (x < CR_of_Q R r -> DDupcut upcut r)
             /\ (CR_of_Q R r < x -> ~DDupcut upcut r) }.
Proof.
  intros.
  assert (forall a b : Q, Qle a b -> Qle (-b) (-a)).
  { intros. apply (Qplus_le_l _ _ (a+b)). ring_simplify. exact H. }
  assert (CR_cauchy R (fun n:nat => CR_of_Q R (proj1_sig (DDcut_limit
                                           upcut (1#Pos.of_nat n) (eq_refl _))))).
  { intros p. exists (Pos.to_nat p). intros i j pi pj.
    destruct (DDcut_limit upcut (1 # Pos.of_nat i) eq_refl),
    (DDcut_limit upcut (1 # Pos.of_nat j) eq_refl); unfold proj1_sig.
    apply (CRabs_le). split.
    - intros. unfold CRminus.
      rewrite <- CR_of_Q_opp, <- CR_of_Q_opp, <- CR_of_Q_plus.
      apply CR_of_Q_le.
      apply (Qplus_le_l _ _ x0). ring_simplify.
      setoid_replace (-1 * (1 # p) + x0)%Q with (x0 - (1 # p))%Q.
      2: ring. apply (Qle_trans _ (x0- (1#Pos.of_nat j))).
      + apply Qplus_le_r. apply H.
        apply Z2Nat.inj_le.
        * discriminate.
        * discriminate.
        * simpl.
          rewrite Nat2Pos.id.
          -- exact pj.
          -- intro abs.
             subst j. inversion pj. pose proof (Pos2Nat.is_pos p).
             rewrite H1 in H0. inversion H0.
      + apply Qlt_le_weak, (DDlow_below_up upcut).
        * apply a.
        * apply a0.
    - unfold CRminus. rewrite <- CR_of_Q_opp, <- CR_of_Q_plus.
      apply CR_of_Q_le.
      apply (Qplus_le_l _ _ (x0-(1#p))). ring_simplify.
      setoid_replace (x -1 * (1 # p))%Q with (x - (1 # p))%Q.
      2: ring. apply (Qle_trans _ (x- (1#Pos.of_nat i))).
      + apply Qplus_le_r. apply H.
        apply Z2Nat.inj_le.
        * discriminate.
        * discriminate.
        * simpl.
          rewrite Nat2Pos.id.
          -- exact pi.
          -- intro abs.
             subst i. inversion pi. pose proof (Pos2Nat.is_pos p).
             rewrite H1 in H0. inversion H0.
      + apply Qlt_le_weak, (DDlow_below_up upcut).
        * apply a0.
        * apply a. }
  apply CR_complete in H0. destruct H0 as [l lcv].
  exists l. split.
  - intros. (* find an upper point between the limit and r *)
    destruct (CR_cv_open_above _ (CR_of_Q R r) l lcv H0) as [p pmaj].
    specialize (pmaj p (Nat.le_refl p)).
    unfold proj1_sig in pmaj.
    destruct (DDcut_limit upcut (1 # Pos.of_nat p) eq_refl) as [q qmaj].
    apply (DDinterval upcut q). 2: apply qmaj.
    destruct (Q_dec q r).
    + destruct s.
      * apply Qlt_le_weak, q0.
      * exfalso. apply (CR_of_Q_lt R) in q0. exact (CRlt_asym _ _ pmaj q0).
    + rewrite q0. apply Qle_refl.
   - intros H0 abs.
    assert ((CR_of_Q R r+l) * CR_of_Q R (1#2) < l).
    { apply (CRmult_lt_reg_r (CR_of_Q R 2)).
      - apply CR_of_Q_pos. reflexivity.
      - rewrite CRmult_assoc, <- CR_of_Q_mult, (CR_of_Q_plus R 1 1).
        setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
        rewrite CRmult_plus_distr_l, CRmult_1_r, CRmult_1_r.
        apply CRplus_lt_compat_r. exact H0. }
    destruct (CR_cv_open_below _ _ l lcv H1) as [p pmaj].
    assert (0 < (l-CR_of_Q R r) * CR_of_Q R (1#2)).
    { apply CRmult_lt_0_compat.
      - rewrite <- (CRplus_opp_r (CR_of_Q R r)).
        apply CRplus_lt_compat_r. exact H0.
      - apply CR_of_Q_pos. reflexivity. }
    destruct (CRup_nat (CRinv R _ (inr H2))) as [i imaj].
    destruct i.
     + exfalso. simpl in imaj.
       exact (CRlt_asym _ _ imaj (CRinv_0_lt_compat R _ (inr H2) H2)).
     + specialize (pmaj (max (S i) (S p)) (Nat.le_trans p (S p) _ (le_S p p (Nat.le_refl p)) (Nat.le_max_r (S i) (S p)))).
       unfold proj1_sig in pmaj.
       destruct (DDcut_limit upcut (1 # Pos.of_nat (max (S i) (S p))) eq_refl)
         as [q qmaj].
       destruct qmaj. apply H4. clear H4.
       apply (DDinterval upcut r). 2: exact abs.
       apply (Qplus_le_l _ _ (1 # Pos.of_nat (Init.Nat.max (S i) (S p)))).
       ring_simplify. apply (Qle_trans _ (r + (1 # Pos.of_nat (S i)))).
       * rewrite Qplus_le_r. unfold Qle,Qnum,Qden.
         rewrite Z.mul_1_l, Z.mul_1_l. apply Pos2Z.pos_le_pos.
         apply Pos2Nat.inj_le. rewrite Nat2Pos.id, Nat2Pos.id.
         -- apply Nat.le_max_l.
         -- discriminate.
         -- discriminate.
       * apply (CRmult_lt_compat_l ((l - CR_of_Q R r) * CR_of_Q R (1 # 2))) in imaj.
         2: exact H2.
         rewrite CRinv_r in imaj.
         destruct (Q_dec (r+(1#Pos.of_nat (S i))) q);[|rewrite q0; apply Qle_refl].
         destruct s.
         { apply Qlt_le_weak, q0. }
         exfalso. apply (CR_of_Q_lt R) in q0.
         apply (CRlt_asym _ _ pmaj). apply (CRlt_le_trans _ _ _ q0).
         apply (CRplus_le_reg_l (-CR_of_Q R r)).
         rewrite CR_of_Q_plus, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
         apply (CRmult_lt_compat_r (CR_of_Q R (1 # Pos.of_nat (S i)))) in imaj.
         -- rewrite CRmult_1_l in imaj.
            apply (CRle_trans _ (
                             (l - CR_of_Q R r) * CR_of_Q R (1 # 2) * CR_of_Q R (Z.of_nat (S i) # 1) *
                               CR_of_Q R (1 # Pos.of_nat (S i)))).
            ++ apply CRlt_asym, imaj.
            ++ rewrite CRmult_assoc, <- CR_of_Q_mult.
               setoid_replace ((Z.of_nat (S i) # 1) * (1 # Pos.of_nat (S i)))%Q with 1%Q.
               ** rewrite CRmult_1_r.
                  unfold CRminus. rewrite CRmult_plus_distr_r, (CRplus_comm (-CR_of_Q R r)).
                  rewrite (CRplus_comm (CR_of_Q R r)), CRmult_plus_distr_r.
                  rewrite CRplus_assoc. apply CRplus_le_compat_l.
                  rewrite <- CR_of_Q_mult, <- CR_of_Q_opp, <- CR_of_Q_mult, <- CR_of_Q_plus.
                  apply CR_of_Q_le. ring_simplify. apply Qle_refl.
               ** unfold Qeq, Qmult, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
                  rewrite Z.mul_1_l, Pos.mul_1_l. unfold Z.of_nat.
                  apply f_equal. apply Pos.of_nat_succ.
         -- apply CR_of_Q_pos. reflexivity.
Qed.

Lemma is_upper_bound_glb :
  forall {R : ConstructiveReals} (E:CRcarrier R -> Prop),
    sig_not_dec_T
    -> sig_forall_dec_T
    -> (exists x : CRcarrier R, E x)
    -> (exists x : CRcarrier R, is_upper_bound E x)
    -> { x : CRcarrier R
      | forall r:Q, (x < CR_of_Q R r -> is_upper_bound E (CR_of_Q R r))
               /\ (CR_of_Q R r < x -> ~is_upper_bound E (CR_of_Q R r)) }.
Proof.
  intros R E sig_not_dec lpo Einhab Ebound.
  destruct (is_upper_bound_epsilon E lpo sig_not_dec Ebound) as [a luba].
  destruct (is_upper_bound_not_epsilon E lpo sig_not_dec Einhab) as [b glbb].
  pose (fun q => is_upper_bound E (CR_of_Q R q)) as upcut.
  assert (forall q:Q, { upcut q } + { ~upcut q } ).
  { intro q. apply is_upper_bound_dec.
    - exact lpo.
    - exact sig_not_dec. }
  assert (forall q r : Q, (q <= r)%Q -> upcut q -> upcut r).
  { intros. intros x Ex. specialize (H1 x Ex). intro abs.
    apply H1. apply (CRle_lt_trans _ (CR_of_Q R r)). 2: exact abs.
    apply CR_of_Q_le. exact H0. }
  assert (upcut (Z.of_nat a # 1)%Q).
  { intros x Ex. exact (luba x Ex). }
  assert (~upcut (- Z.of_nat b # 1)%Q).
  { intros abs. apply glbb. intros x Ex.
    specialize (abs x Ex). rewrite <- CR_of_Q_opp.
    exact abs. }
  assert (forall q r : Q, (q == r)%Q -> upcut q -> upcut r).
  { intros. intros x Ex. specialize (H4 x Ex). rewrite <- H3. exact H4. }
  destruct (@glb_dec_Q R (Build_DedekindDecCut
                            upcut H3 (-Z.of_nat b # 1)%Q (Z.of_nat a # 1)
                            H H0 H1 H2)).
  simpl in a0. exists x. intro r. split.
  - intros. apply a0. exact H4.
  - intros H6 abs. specialize (a0 r) as [_ a0]. apply a0.
    + exact H6.
    + exact abs.
Qed.

Lemma is_upper_bound_closed :
  forall {R : ConstructiveReals}
    (E:CRcarrier R -> Prop) (sig_forall_dec : sig_forall_dec_T)
    (sig_not_dec : sig_not_dec_T)
    (Einhab : exists x : CRcarrier R, E x)
    (Ebound : exists x : CRcarrier R, is_upper_bound E x),
    is_lub
      E (proj1_sig (is_upper_bound_glb
                      E sig_not_dec sig_forall_dec Einhab Ebound)).
Proof.
  intros. split.
  - intros x Ex.
    destruct (is_upper_bound_glb E sig_not_dec sig_forall_dec Einhab Ebound); simpl.
    intro abs. destruct (CR_Q_dense R x0 x abs) as [q [qmaj H]].
    specialize (a q) as [a _]. specialize (a qmaj x Ex).
    contradiction.
  - intros.
    destruct (is_upper_bound_glb E sig_not_dec sig_forall_dec Einhab Ebound); simpl.
    intro abs. destruct (CR_Q_dense R b x abs) as [q [qmaj H0]].
    specialize (a q) as [_ a]. apply a.
    + exact H0.
    + intros y Ey. specialize (H y Ey). intro abs2.
      apply H. exact (CRlt_trans _ (CR_of_Q R q) _ qmaj abs2).
Qed.

Lemma sig_lub :
  forall {R : ConstructiveReals} (E:CRcarrier R -> Prop),
    sig_forall_dec_T
    -> sig_not_dec_T
    -> (exists x : CRcarrier R, E x)
    -> (exists x : CRcarrier R, is_upper_bound E x)
    -> { u : CRcarrier R | is_lub E u }.
Proof.
  intros R E sig_forall_dec sig_not_dec Einhab Ebound.
  pose proof (is_upper_bound_closed E sig_forall_dec sig_not_dec Einhab Ebound).
  destruct (is_upper_bound_glb
              E sig_not_dec sig_forall_dec Einhab Ebound); simpl in H.
  exists x. exact H.
Qed.

Definition CRis_upper_bound {R : ConstructiveReals} (E:CRcarrier R -> Prop) (m:CRcarrier R)
  := forall x:CRcarrier R, E x -> CRlt R m x -> False.

Lemma CR_sig_lub :
  forall {R : ConstructiveReals} (E:CRcarrier R -> Prop),
    (forall x y : CRcarrier R, CReq R x y -> (E x <-> E y))
    -> sig_forall_dec_T
    -> sig_not_dec_T
    -> (exists x : CRcarrier R, E x)
    -> (exists x : CRcarrier R, CRis_upper_bound E x)
    -> { u : CRcarrier R | CRis_upper_bound E u /\
                           forall y:CRcarrier R, CRis_upper_bound E y -> CRlt R y u -> False }.
Proof.
  intros. exact (sig_lub E X X0 H0 H1).
Qed.
