(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(************************************************************************)

(* Proof that LPO and the excluded middle for negations imply
   the existence of least upper bounds for all non-empty and bounded
   subsets of the real numbers. *)

Require Import QArith_base.
Require Import Qabs.
Require Import ConstructiveReals.
Require Import ConstructiveCauchyRealsMult.
Require Import ConstructiveRealsMorphisms.
Require Import ConstructiveRcomplete.
Require Import Logic.ConstructiveEpsilon.

Local Open Scope CReal_scope.

Definition sig_forall_dec_T : Type
  := forall (P : nat -> Prop), (forall n, {P n} + {~P n})
                   -> {n | ~P n} + {forall n, P n}.

Definition sig_not_dec_T : Type := forall P : Prop, { ~~P } + { ~P }.

Definition is_upper_bound (E:CReal -> Prop) (m:CReal)
  := forall x:CReal, E x -> x <= m.

Definition is_lub (E:CReal -> Prop) (m:CReal) :=
  is_upper_bound E m /\ (forall b:CReal, is_upper_bound E b -> m <= b).

Lemma is_upper_bound_dec :
  forall (E:CReal -> Prop) (x:CReal),
    sig_forall_dec_T
    -> sig_not_dec_T
    -> { is_upper_bound E x } + { ~is_upper_bound E x }.
Proof.
  intros E x lpo sig_not_dec.
  destruct (sig_not_dec (~exists y:CReal, E y /\ CRealLtProp x y)).
  - left. intros y H.
    destruct (CRealLt_lpo_dec x y lpo). 2: exact f.
    exfalso. apply n. intro abs. apply abs.
    exists y. split. exact H. destruct c. exists x0. exact q.
  - right. intro abs. apply n. intros [y [H H0]].
    specialize (abs y H). apply CRealLtEpsilon in H0. contradiction.
Qed.

Lemma is_upper_bound_epsilon :
  forall (E:CReal -> Prop),
    sig_forall_dec_T
    -> sig_not_dec_T
    -> (exists x:CReal, is_upper_bound E x)
    -> { n:nat | is_upper_bound E (inject_Q (Z.of_nat n # 1)) }.
Proof.
  intros E lpo sig_not_dec Ebound.
  apply constructive_indefinite_ground_description_nat.
  - intro n. apply is_upper_bound_dec. exact lpo. exact sig_not_dec.
  - destruct Ebound as [x H]. destruct (Rup_pos x). exists (Pos.to_nat x0).
    intros y ey. specialize (H y ey).
    apply CRealLt_asym. apply (CReal_le_lt_trans _ x).
    exact H. rewrite positive_nat_Z. exact c.
Qed.

Lemma is_upper_bound_not_epsilon :
  forall E:CReal -> Prop,
    sig_forall_dec_T
    -> sig_not_dec_T
    -> (exists x : CReal, E x)
    -> { m:nat | ~is_upper_bound E (-inject_Q (Z.of_nat m # 1)) }.
Proof.
  intros E lpo sig_not_dec H.
  apply constructive_indefinite_ground_description_nat.
  - intro n. destruct (is_upper_bound_dec E (-inject_Q (Z.of_nat n # 1)) lpo sig_not_dec).
    right. intro abs. contradiction. left. exact n0.
  - destruct H as [x H]. destruct (Rup_pos (-x)) as [n H0].
    exists (Pos.to_nat n). intro abs. specialize (abs x H).
    apply abs. rewrite positive_nat_Z.
    apply (CReal_plus_lt_reg_l (inject_Q (Z.pos n # 1)-x)).
    ring_simplify. exact H0.
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
  intros. destruct (Qlt_le_dec b a). exact q.
  exfalso. apply H0. apply (DDinterval upcut a).
  exact q. exact H.
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
      exact H0. intro abs.
      apply (DDproper upcut _ (DDlow upcut + (Z.of_nat n # 1) * r)) in abs.
      contradiction.
      rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite <- Qinv_plus_distr.
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
  apply (DDinterval upcut (DDhigh upcut)). 2: exact (DDhighProp upcut).
  apply Qlt_le_weak. apply (Qplus_lt_r _ _ (-DDlow upcut)).
  rewrite Qplus_assoc, <- (Qplus_comm (DDlow upcut)), Qplus_opp_r,
  Qplus_0_l, Qplus_comm.
  rewrite positive_nat_Z. exact nmaj.
  intros abs. rewrite abs in H. exact (Qlt_irrefl 0 H).
Qed.

Lemma glb_dec_Q : forall upcut : DedekindDecCut,
    { x : CReal | forall r:Q, (x < inject_Q r -> DDupcut upcut r)
                         /\ (inject_Q r < x -> ~DDupcut upcut r) }.
Proof.
  intros.
  assert (forall a b : Q, Qle a b -> Qle (-b) (-a)).
  { intros. apply (Qplus_le_l _ _ (a+b)). ring_simplify. exact H. }
  assert (QCauchySeq (fun n:nat => proj1_sig (DDcut_limit
                                           upcut (1#Pos.of_nat n) (eq_refl _)))
                     Pos.to_nat).
  { intros p i j pi pj.
    destruct (DDcut_limit upcut (1 # Pos.of_nat i) eq_refl),
    (DDcut_limit upcut (1 # Pos.of_nat j) eq_refl); unfold proj1_sig.
    apply Qabs_case. intros.
    apply (Qplus_lt_l _ _ (x0- (1#p))). ring_simplify.
    setoid_replace (x + -1 * (1 # p))%Q with (x - (1 # p))%Q.
    2: ring. apply (Qle_lt_trans _ (x- (1#Pos.of_nat i))).
    apply Qplus_le_r. apply H.
    apply Z2Nat.inj_le. discriminate. discriminate. simpl.
    rewrite Nat2Pos.id. exact pi. intro abs.
    subst i. inversion pi. pose proof (Pos2Nat.is_pos p).
    rewrite H2 in H1. inversion H1.
    apply (DDlow_below_up upcut). apply a0. apply a.
    intros.
    apply (Qplus_lt_l _ _ (x- (1#p))). ring_simplify.
    setoid_replace (x0 + -1 * (1 # p))%Q with (x0 - (1 # p))%Q.
    2: ring. apply (Qle_lt_trans _ (x0- (1#Pos.of_nat j))).
    apply Qplus_le_r. apply H.
    apply Z2Nat.inj_le. discriminate. discriminate. simpl.
    rewrite Nat2Pos.id. exact pj. intro abs.
    subst j. inversion pj. pose proof (Pos2Nat.is_pos p).
    rewrite H2 in H1. inversion H1.
    apply (DDlow_below_up upcut). apply a. apply a0. }
  pose (exist (fun qn => QSeqEquiv qn qn Pos.to_nat) _ H0) as l.
  exists l. split.
  - intros. (* find an upper point between the limit and r *)
    destruct H1 as [p pmaj].
    unfold l,proj1_sig in pmaj.
    destruct (DDcut_limit upcut (1 # Pos.of_nat (Pos.to_nat p)) eq_refl) as [q qmaj]
    ; simpl in pmaj.
    apply (DDinterval upcut q). 2: apply qmaj.
    apply (Qplus_lt_l _ _ q) in pmaj. ring_simplify in pmaj.
    apply (Qle_trans _ ((2#p) + q)).
    apply (Qplus_le_l _ _ (-q)). ring_simplify. discriminate.
    apply Qlt_le_weak. exact pmaj.
  - intros [p pmaj] abs.
    unfold l,proj1_sig in pmaj.
    destruct (DDcut_limit upcut (1 # Pos.of_nat (Pos.to_nat p)) eq_refl) as [q qmaj]
    ; simpl in pmaj.
    rewrite Pos2Nat.id in qmaj.
    apply (Qplus_lt_r _ _ (r - (2#p))) in pmaj. ring_simplify in pmaj.
    destruct qmaj. apply H2.
    apply (DDinterval upcut r). 2: exact abs.
    apply Qlt_le_weak, (Qlt_trans _ (-1*(2#p) + q) _ pmaj).
    apply (Qplus_lt_l _ _ ((2#p) -q)). ring_simplify.
    setoid_replace (-1 * (1 # p))%Q with (-(1#p))%Q.
    2: ring. rewrite Qinv_minus_distr. reflexivity.
Qed.

Lemma is_upper_bound_glb :
  forall (E:CReal -> Prop),
    sig_not_dec_T
    -> sig_forall_dec_T
    -> (exists x : CReal, E x)
    -> (exists x : CReal, is_upper_bound E x)
    -> { x : CReal | forall r:Q, (x < inject_Q r -> is_upper_bound E (inject_Q r))
                           /\ (inject_Q r < x -> ~is_upper_bound E (inject_Q r)) }.
Proof.
  intros E sig_not_dec lpo Einhab Ebound.
  destruct (is_upper_bound_epsilon E lpo sig_not_dec Ebound) as [a luba].
  destruct (is_upper_bound_not_epsilon E lpo sig_not_dec Einhab) as [b glbb].
  pose (fun q => is_upper_bound E (inject_Q q)) as upcut.
  assert (forall q:Q, { upcut q } + { ~upcut q } ).
  { intro q. apply is_upper_bound_dec. exact lpo. exact sig_not_dec. }
  assert (forall q r : Q, (q <= r)%Q -> upcut q -> upcut r).
  { intros. intros x Ex. specialize (H1 x Ex). intro abs.
    apply H1. apply (CReal_le_lt_trans _ (inject_Q r)). 2: exact abs.
    apply inject_Q_le. exact H0. }
  assert (upcut (Z.of_nat a # 1)%Q).
  { intros x Ex. exact (luba x Ex). }
  assert (~upcut (- Z.of_nat b # 1)%Q).
  { intros abs. apply glbb. intros x Ex.
    specialize (abs x Ex). rewrite <- opp_inject_Q.
    exact abs. }
  assert (forall q r : Q, (q == r)%Q -> upcut q -> upcut r).
  { intros. intros x Ex. specialize (H4 x Ex). rewrite <- H3. exact H4. }
  destruct (glb_dec_Q (Build_DedekindDecCut
                         upcut H3 (-Z.of_nat b # 1)%Q (Z.of_nat a # 1)
                         H H0 H1 H2)).
  simpl in a0. exists x. intro r. split.
  - intros. apply a0. exact H4.
  - intros H6 abs. specialize (a0 r) as [_ a0]. apply a0.
    exact H6. exact abs.
Qed.

Lemma is_upper_bound_closed :
  forall (E:CReal -> Prop) (sig_forall_dec : sig_forall_dec_T)
    (sig_not_dec : sig_not_dec_T)
    (Einhab : exists x : CReal, E x)
    (Ebound : exists x : CReal, is_upper_bound E x),
    is_lub
      E (proj1_sig (is_upper_bound_glb
                      E sig_not_dec sig_forall_dec Einhab Ebound)).
Proof.
  intros. split.
  - intros x Ex.
    destruct (is_upper_bound_glb E sig_not_dec sig_forall_dec Einhab Ebound); simpl.
    intro abs. destruct (FQ_dense x0 x abs) as [q [qmaj H]].
    specialize (a q) as [a _]. specialize (a qmaj x Ex).
    contradiction.
  - intros.
    destruct (is_upper_bound_glb E sig_not_dec sig_forall_dec Einhab Ebound); simpl.
    intro abs. destruct (FQ_dense b x abs) as [q [qmaj H0]].
    specialize (a q) as [_ a]. apply a. exact H0.
    intros y Ey. specialize (H y Ey). intro abs2.
    apply H. exact (CReal_lt_trans _ (inject_Q q) _ qmaj abs2).
Qed.

Lemma sig_lub :
  forall (E:CReal -> Prop),
    sig_forall_dec_T
    -> sig_not_dec_T
    -> (exists x : CReal, E x)
    -> (exists x : CReal, is_upper_bound E x)
    -> { u : CReal | is_lub E u }.
Proof.
  intros E sig_forall_dec sig_not_dec Einhab Ebound.
  pose proof (is_upper_bound_closed E sig_forall_dec sig_not_dec Einhab Ebound).
  destruct (is_upper_bound_glb
              E sig_not_dec sig_forall_dec Einhab Ebound); simpl in H.
  exists x. exact H.
Qed.

Definition CRis_upper_bound (R : ConstructiveReals) (E:CRcarrier R -> Prop) (m:CRcarrier R)
  := forall x:CRcarrier R, E x -> CRlt R m x -> False.

Lemma CR_sig_lub :
  forall (R : ConstructiveReals) (E:CRcarrier R -> Prop),
    (forall x y : CRcarrier R, orderEq _ (CRlt R) x y -> (E x <-> E y))
    -> sig_forall_dec_T
    -> sig_not_dec_T
    -> (exists x : CRcarrier R, E x)
    -> (exists x : CRcarrier R, CRis_upper_bound R E x)
    -> { u : CRcarrier R | CRis_upper_bound R E u /\
                           forall y:CRcarrier R, CRis_upper_bound R E y -> CRlt R y u -> False }.
Proof.
  intros. destruct (sig_lub (fun x:CReal => E (CauchyMorph R x)) X X0) as [u ulub].
  - destruct H0. exists (CauchyMorph_inv R x).
    specialize (H (CauchyMorph R (CauchyMorph_inv R x)) x
                  (CauchyMorph_surject R x)) as [_ H].
    exact (H H0).
  - destruct H1. exists (CauchyMorph_inv R x).
    intros y Ey. specialize (H1 (CauchyMorph R y) Ey).
    intros abs. apply H1.
    apply (CauchyMorph_increasing R) in abs.
    apply (CRle_lt_trans R _ (CauchyMorph R (CauchyMorph_inv R x))).
    2: exact abs. apply (CauchyMorph_surject R x).
  - exists (CauchyMorph R u). destruct ulub. split.
    + intros y Ey abs. specialize (H2 (CauchyMorph_inv R y)).
      simpl in H2.
      specialize (H (CauchyMorph R (CauchyMorph_inv R y)) y
                    (CauchyMorph_surject R y)) as [_ H].
      specialize (H2 (H Ey)). apply H2.
      apply CauchyMorph_inv_increasing in abs.
      rewrite CauchyMorph_inject in abs. exact abs.
    + intros. apply (H3 (CauchyMorph_inv R y)).
      intros z Ez abs. specialize (H4 (CauchyMorph R z)).
      apply (H4 Ez). apply (CauchyMorph_increasing R) in abs.
      apply (CRle_lt_trans R _ (CauchyMorph R (CauchyMorph_inv R y))).
      2: exact abs. apply (CauchyMorph_surject R y).
      apply CauchyMorph_inv_increasing in H5.
      rewrite CauchyMorph_inject in H5. exact H5.
Qed.
