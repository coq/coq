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

(** An interface for constructive and computable real numbers.
    All of its instances are isomorphic (see file ConstructiveRealsMorphisms).
    For example it contains the Cauchy reals implemented in file
    ConstructivecauchyReals and the sumbool-based Dedekind reals defined by

Structure R := {
  (* The cuts are represented as propositional functions, rather than subsets,
     as there are no subsets in type theory. *)
  lower : Q -> Prop;
  upper : Q -> Prop;
  (* The cuts respect equality on Q. *)
  lower_proper : Proper (Qeq ==> iff) lower;
  upper_proper : Proper (Qeq ==> iff) upper;
  (* The cuts are inhabited. *)
  lower_bound : { q : Q | lower q };
  upper_bound : { r : Q | upper r };
  (* The lower cut is a lower set. *)
  lower_lower : forall q r, q < r -> lower r -> lower q;
  (* The lower cut is open. *)
  lower_open : forall q, lower q -> exists r, q < r /\ lower r;
  (* The upper cut is an upper set. *)
  upper_upper : forall q r, q < r -> upper q -> upper r;
  (* The upper cut is open. *)
  upper_open : forall r, upper r -> exists q,  q < r /\ upper q;
  (* The cuts are disjoint. *)
  disjoint : forall q, ~ (lower q /\ upper q);
  (* There is no gap between the cuts. *)
  located : forall q r, q < r -> { lower q } + { upper r }
}.

  see github.com/andrejbauer/dedekind-reals for the Prop-based
  version of those Dedekind reals (although Prop fails to make
  them an instance of ConstructiveReals).

  Any computation about constructive reals, can be worked
  in the fastest instance for it; we then transport the results
  to all other instances by the isomorphisms. This way of working
  is different from the usual interfaces, where we would rather
  prove things abstractly, by quantifying universally on the instance.

  The functions of ConstructiveReals do not have a direct impact
  on performance, because algorithms will be extracted from instances,
  and because fast ConstructiveReals morphisms should be coded
  manually. However, since instances are forced to implement
  those functions, it is probable that they will also use them
  in their algorithms. So those functions hint at what we think
  will yield fast and small extracted programs. *)


Require Import QArith.

Definition isLinearOrder (X : Set) (Xlt : X -> X -> Set) : Set
  := (forall x y:X, Xlt x y -> Xlt y x -> False)
     * (forall x y z : X, Xlt x y -> Xlt y z -> Xlt x z)
     * (forall x y z : X, Xlt x z -> Xlt x y + Xlt y z).

Definition orderEq (X : Set) (Xlt : X -> X -> Set) (x y : X) : Prop
  := (Xlt x y -> False) /\ (Xlt y x -> False).

Definition orderAppart (X : Set) (Xlt : X -> X -> Set) (x y : X) : Set
  := Xlt x y  +  Xlt y x.

Definition orderLe (X : Set) (Xlt : X -> X -> Set) (x y : X) : Prop
  := Xlt y x -> False.

Definition sig_forall_dec_T : Type
  := forall (P : nat -> Prop), (forall n, {P n} + {~P n})
                   -> {n | ~P n} + {forall n, P n}.

Definition sig_not_dec_T : Type := forall P : Prop, { ~~P } + { ~P }.

Record ConstructiveReals : Type :=
  {
    CRcarrier : Set;

    (* Put this order relation in sort Set rather than Prop,
       to allow the definition of fast ConstructiveReals morphisms.
       For example, the Cauchy reals do store information in
       the proofs of CRlt, which is used in algorithms in sort Set. *)
    CRlt : CRcarrier -> CRcarrier -> Set;
    CRltLinear : isLinearOrder CRcarrier CRlt;

    (* The propositional truncation of CRlt. It facilitates proofs
       when computations are not considered important, for example in
       classical reals with extra logical axioms. *)
    CRltProp : CRcarrier -> CRcarrier -> Prop;
    (* This choice algorithm can be slow, keep it for the classical
       quotient of the reals, where computations are blocked by
       axioms like LPO. *)
    CRltEpsilon : forall x y : CRcarrier, CRltProp x y -> CRlt x y;
    CRltForget : forall x y : CRcarrier, CRlt x y -> CRltProp x y;
    CRltDisjunctEpsilon : forall a b c d : CRcarrier,
        (CRltProp a b \/ CRltProp c d) -> CRlt a b  +  CRlt c d;

    (* Constants *)
    CRzero : CRcarrier;
    CRone : CRcarrier;

    (* Addition and multiplication *)
    CRplus : CRcarrier -> CRcarrier -> CRcarrier;
    CRopp : CRcarrier -> CRcarrier; (* Computable opposite,
                         stronger than Prop-existence of opposite *)
    CRmult : CRcarrier -> CRcarrier -> CRcarrier;

    CRisRing : ring_theory CRzero CRone CRplus CRmult
                          (fun x y => CRplus x (CRopp y)) CRopp (orderEq CRcarrier CRlt);
    CRisRingExt : ring_eq_ext CRplus CRmult CRopp (orderEq CRcarrier CRlt);

    (* Compatibility with order *)
    CRzero_lt_one : CRlt CRzero CRone; (* 0 # 1 would only allow 0 < 1 because
                                    of Fmult_lt_0_compat so request 0 < 1 directly. *)
    CRplus_lt_compat_l : forall r r1 r2 : CRcarrier,
        CRlt r1 r2 -> CRlt (CRplus r r1) (CRplus r r2);
    CRplus_lt_reg_l : forall r r1 r2 : CRcarrier,
        CRlt (CRplus r r1) (CRplus r r2) -> CRlt r1 r2;
    CRmult_lt_0_compat : forall x y : CRcarrier,
        CRlt CRzero x -> CRlt CRzero y -> CRlt CRzero (CRmult x y);

    (* A constructive total inverse function on F would need to be continuous,
       which is impossible because we cannot connect plus and minus infinities.
       Therefore it has to be a partial function, defined on non zero elements.
       For this reason we cannot use Coq's field_theory and field tactic.

       To implement Finv by Cauchy sequences we need orderAppart,
       ~orderEq is not enough. *)
    CRinv : forall x : CRcarrier, orderAppart _ CRlt x CRzero -> CRcarrier;
    CRinv_l : forall (r:CRcarrier) (rnz : orderAppart _ CRlt r CRzero),
        orderEq _ CRlt (CRmult (CRinv r rnz) r) CRone;
    CRinv_0_lt_compat : forall (r : CRcarrier) (rnz : orderAppart _ CRlt r CRzero),
        CRlt CRzero r -> CRlt CRzero (CRinv r rnz);

    (* The initial field morphism (in characteristic zero).
       The abstract definition by iteration of addition is
       probably the slowest. Let each instance implement
       a faster (and often simpler) version. *)
    CR_of_Q : Q -> CRcarrier;
    CR_of_Q_plus : forall q r : Q, orderEq _ CRlt (CR_of_Q (q+r))
                                           (CRplus (CR_of_Q q) (CR_of_Q r));
    CR_of_Q_mult : forall q r : Q, orderEq _ CRlt (CR_of_Q (q*r))
                                           (CRmult (CR_of_Q q) (CR_of_Q r));
    CR_of_Q_one : orderEq _ CRlt (CR_of_Q 1) CRone;
    CR_of_Q_lt : forall q r : Q,
        Qlt q r -> CRlt (CR_of_Q q) (CR_of_Q r);
    lt_CR_of_Q : forall q r : Q,
        CRlt (CR_of_Q q) (CR_of_Q r) -> Qlt q r;

    (* This function is very fast in both the Cauchy and Dedekind
       instances, because this rational number q is almost what
       the proof of CRlt x y contains.
       This function is also the heart of the computation of
       constructive real numbers : it approximates x to any
       requested precision y. *)
    CR_Q_dense : forall x y : CRcarrier, CRlt x y ->
       { q : Q  &  prod (CRlt x (CR_of_Q q))
                        (CRlt (CR_of_Q q) y) };
    CR_archimedean : forall x : CRcarrier,
        { n : positive  &  CRlt x (CR_of_Q (Z.pos n # 1)) };

    CRminus (x y : CRcarrier) : CRcarrier
    := CRplus x (CRopp y);

    (* Definitions of convergence and Cauchy-ness. The formulas
       with orderLe or CRlt are logically equivalent, the choice of
       orderLe in sort Prop is a question of performance.
       It is very rare to turn back to the strict order to
       define functions in sort Set, so we prefer to discard
       those proofs during extraction. And even in those rare cases,
       it is easy to divide epsilon by 2 for example. *)
    CR_cv (un : nat -> CRcarrier) (l : CRcarrier) : Set
    := forall p:positive,
        { n : nat  |  forall i:nat, le n i
                           -> orderLe _ CRlt (CR_of_Q (-1#p)) (CRminus (un i) l)
                             /\ orderLe _ CRlt (CRminus (un i) l) (CR_of_Q (1#p)) };
    CR_cauchy (un : nat -> CRcarrier) : Set
    := forall p : positive,
        { n : nat  |  forall i j:nat, le n i -> le n j
                             -> orderLe _ CRlt (CR_of_Q (-1#p)) (CRminus (un i) (un j))
                               /\ orderLe _ CRlt (CRminus (un i) (un j)) (CR_of_Q (1#p)) };

    (* For the Cauchy reals, this algorithm consists in building
       a Cauchy sequence of rationals un : nat -> Q that has
       the same limit as xn. For each n:nat, un n is a 1/n
       rational approximation of a point of xn that has converged
       within 1/n. *)
    CR_complete :
      forall xn : (nat -> CRcarrier),
        CR_cauchy xn -> { l : CRcarrier  &  CR_cv xn l };
  }.

Lemma CRlt_asym : forall (R : ConstructiveReals) (x y : CRcarrier R),
    CRlt R x y -> CRlt R y x -> False.
Proof.
  intros. destruct (CRltLinear R), p.
  apply (f x y); assumption.
Qed.

Lemma CRlt_proper
  : forall R : ConstructiveReals,
    CMorphisms.Proper
      (CMorphisms.respectful (orderEq _ (CRlt R))
                             (CMorphisms.respectful (orderEq _ (CRlt R)) CRelationClasses.iffT)) (CRlt R).
Proof.
  intros R x y H x0 y0 H0. destruct H, H0.
  destruct (CRltLinear R). split.
  - intro. destruct (s x y x0). assumption.
    contradiction. destruct (s y y0 x0).
    assumption. assumption. contradiction.
  - intro. destruct (s y x y0). assumption.
    contradiction. destruct (s x x0 y0).
    assumption. assumption. contradiction.
Qed.

Lemma CRle_refl : forall (R : ConstructiveReals) (x : CRcarrier R),
    CRlt R x x -> False.
Proof.
  intros. destruct (CRltLinear R), p.
  exact (f x x H H).
Qed.

Lemma CRle_lt_trans : forall (R : ConstructiveReals) (r1 r2 r3 : CRcarrier R),
    (CRlt R r2 r1 -> False) -> CRlt R r2 r3 -> CRlt R r1 r3.
Proof.
  intros. destruct (CRltLinear R).
  destruct (s r2 r1 r3 H0). contradiction. apply c.
Qed.

Lemma CRlt_le_trans : forall (R : ConstructiveReals) (r1 r2 r3 : CRcarrier R),
    CRlt R r1 r2 -> (CRlt R r3 r2 -> False) -> CRlt R r1 r3.
Proof.
  intros. destruct (CRltLinear R).
  destruct (s r1 r3 r2 H). apply c. contradiction.
Qed.

Lemma CRle_trans : forall (R : ConstructiveReals) (x y z : CRcarrier R),
    orderLe _ (CRlt R) x y -> orderLe _ (CRlt R) y z -> orderLe _ (CRlt R) x z.
Proof.
  intros. intro abs. apply H0.
  apply (CRlt_le_trans _ _ x); assumption.
Qed.

Lemma CRlt_trans : forall (R : ConstructiveReals) (x y z : CRcarrier R),
    CRlt R x y -> CRlt R y z -> CRlt R x z.
Proof.
  intros. apply (CRlt_le_trans R _ y _ H).
  apply CRlt_asym. exact H0.
Defined.

Lemma CRlt_trans_flip : forall (R : ConstructiveReals) (x y z : CRcarrier R),
    CRlt R y z -> CRlt R x y -> CRlt R x z.
Proof.
  intros. apply (CRlt_le_trans R _ y). exact H0.
  apply CRlt_asym. exact H.
Defined.

Lemma CReq_refl : forall (R : ConstructiveReals) (x : CRcarrier R),
    orderEq _ (CRlt R) x x.
Proof.
  split; apply CRle_refl.
Qed.

Lemma CReq_sym : forall (R : ConstructiveReals) (x y : CRcarrier R),
    orderEq _ (CRlt R) x y
    -> orderEq _ (CRlt R) y x.
Proof.
  intros. destruct H. split; intro abs; contradiction.
Qed.

Lemma CReq_trans : forall (R : ConstructiveReals) (x y z : CRcarrier R),
    orderEq _ (CRlt R) x y
    -> orderEq _ (CRlt R) y z
    -> orderEq _ (CRlt R) x z.
Proof.
  intros. destruct H,H0. destruct (CRltLinear R), p. split.
  - intro abs. destruct (s _ y _ abs); contradiction.
  - intro abs. destruct (s _ y _ abs); contradiction.
Qed.

Lemma CR_setoid : forall R : ConstructiveReals,
    Setoid_Theory (CRcarrier R) (orderEq _ (CRlt R)).
Proof.
  split. intro x. apply CReq_refl.
  intros x y. apply CReq_sym.
  intros x y z. apply CReq_trans.
Qed.

Lemma CRplus_0_r : forall (R : ConstructiveReals) (x : CRcarrier R),
    orderEq _ (CRlt R) (CRplus R x (CRzero R)) x.
Proof.
  intros. destruct (CRisRing R).
  apply (CReq_trans R _ (CRplus R (CRzero R) x)).
  apply Radd_comm. apply Radd_0_l.
Qed.

Lemma CRmult_1_r : forall (R : ConstructiveReals) (x : CRcarrier R),
    orderEq _ (CRlt R) (CRmult R x (CRone R)) x.
Proof.
  intros. destruct (CRisRing R).
  apply (CReq_trans R _ (CRmult R (CRone R) x)).
  apply Rmul_comm. apply Rmul_1_l.
Qed.

Lemma CRplus_opp_l : forall (R : ConstructiveReals) (x : CRcarrier R),
    orderEq _ (CRlt R) (CRplus R (CRopp R x) x) (CRzero R).
Proof.
  intros. destruct (CRisRing R).
  apply (CReq_trans R _ (CRplus R x (CRopp R x))).
  apply Radd_comm. apply Ropp_def.
Qed.

Lemma CRplus_lt_compat_r : forall (R : ConstructiveReals) (r r1 r2 : CRcarrier R),
    CRlt R r1 r2 -> CRlt R (CRplus R r1 r) (CRplus R r2 r).
Proof.
  intros. destruct (CRisRing R).
  apply (CRlt_proper R (CRplus R r r1) (CRplus R r1 r) (Radd_comm _ _)
                     (CRplus R r2 r) (CRplus R r2 r)).
  apply CReq_refl.
  apply (CRlt_proper R _ _ (CReq_refl _ _) _ (CRplus R r r2)).
  apply Radd_comm. apply CRplus_lt_compat_l. exact H.
Qed.

Lemma CRplus_lt_reg_r : forall (R : ConstructiveReals) (r r1 r2 : CRcarrier R),
    CRlt R (CRplus R r1 r) (CRplus R r2 r) -> CRlt R r1 r2.
Proof.
  intros. destruct (CRisRing R).
  apply (CRlt_proper R (CRplus R r r1) (CRplus R r1 r) (Radd_comm _ _)
                     (CRplus R r2 r) (CRplus R r2 r)) in H.
  2: apply CReq_refl.
  apply (CRlt_proper R _ _ (CReq_refl _ _) _ (CRplus R r r2)) in H.
  apply CRplus_lt_reg_l in H. exact H.
  apply Radd_comm.
Qed.

Lemma CRplus_le_compat_l : forall (R : ConstructiveReals) (r r1 r2 : CRcarrier R),
    orderLe _ (CRlt R) r1 r2
    -> orderLe _ (CRlt R) (CRplus R r r1) (CRplus R r r2).
Proof.
  intros. intros abs. apply CRplus_lt_reg_l in abs. apply H. exact abs.
Qed.

Lemma CRplus_le_compat_r : forall (R : ConstructiveReals) (r r1 r2 : CRcarrier R),
    orderLe _ (CRlt R) r1 r2
    -> orderLe _ (CRlt R) (CRplus R r1 r) (CRplus R r2 r).
Proof.
  intros. intros abs. apply CRplus_lt_reg_r in abs. apply H. exact abs.
Qed.

Lemma CRplus_le_reg_l : forall (R : ConstructiveReals) (r r1 r2 : CRcarrier R),
    orderLe _ (CRlt R) (CRplus R r r1) (CRplus R r r2)
    -> orderLe _ (CRlt R) r1 r2.
Proof.
  intros. intro abs. apply H. clear H.
  apply CRplus_lt_compat_l. exact abs.
Qed.

Lemma CRplus_le_reg_r : forall (R : ConstructiveReals) (r r1 r2 : CRcarrier R),
    orderLe _ (CRlt R) (CRplus R r1 r) (CRplus R r2 r)
    -> orderLe _ (CRlt R) r1 r2.
Proof.
  intros. intro abs. apply H. clear H.
  apply CRplus_lt_compat_r. exact abs.
Qed.

Lemma CRplus_lt_le_compat :
  forall (R : ConstructiveReals) (r1 r2 r3 r4 : CRcarrier R),
    CRlt R r1 r2
    -> (CRlt R r4 r3 -> False)
    -> CRlt R (CRplus R r1 r3) (CRplus R r2 r4).
Proof.
  intros. apply (CRlt_le_trans R _ (CRplus R r2 r3)).
  apply CRplus_lt_compat_r. exact H. intro abs.
  apply CRplus_lt_reg_l in abs. contradiction.
Qed.

Lemma CRplus_eq_reg_l : forall (R : ConstructiveReals) (r r1 r2 : CRcarrier R),
    orderEq _ (CRlt R) (CRplus R r r1) (CRplus R r r2)
    -> orderEq _ (CRlt R) r1 r2.
Proof.
  intros.
  destruct (CRisRingExt R). clear Rmul_ext Ropp_ext.
  pose proof (Radd_ext
                (CRopp R r) (CRopp R r) (CReq_refl _ _)
                _ _ H).
  destruct (CRisRing R).
  apply (CReq_trans _ r1) in H0.
  apply (CReq_trans R _ _ _ H0).
  apply (CReq_trans R _ (CRplus R (CRplus R (CRopp R r) r) r2)).
  apply Radd_assoc.
  apply (CReq_trans R _ (CRplus R (CRzero R) r2)).
  apply Radd_ext. apply CRplus_opp_l. apply CReq_refl.
  apply Radd_0_l. apply CReq_sym.
  apply (CReq_trans R _ (CRplus R (CRplus R (CRopp R r) r) r1)).
  apply Radd_assoc.
  apply (CReq_trans R _ (CRplus R (CRzero R) r1)).
  apply Radd_ext. apply CRplus_opp_l. apply CReq_refl.
  apply Radd_0_l.
Qed.

Lemma CRplus_eq_reg_r : forall (R : ConstructiveReals) (r r1 r2 : CRcarrier R),
    orderEq _ (CRlt R) (CRplus R r1 r) (CRplus R r2 r)
    -> orderEq _ (CRlt R) r1 r2.
Proof.
  intros. apply (CRplus_eq_reg_l R r).
  apply (CReq_trans R _ (CRplus R r1 r)). apply (Radd_comm (CRisRing R)).
  apply (CReq_trans R _ (CRplus R r2 r)).
  exact H. apply (Radd_comm (CRisRing R)).
Qed.

Lemma CRopp_involutive : forall (R : ConstructiveReals) (r : CRcarrier R),
    orderEq _ (CRlt R) (CRopp R (CRopp R r)) r.
Proof.
  intros. apply (CRplus_eq_reg_l R (CRopp R r)).
  apply (CReq_trans R _ (CRzero R)). apply CRisRing.
  apply CReq_sym, (CReq_trans R _ (CRplus R r (CRopp R r))).
  apply CRisRing. apply CRisRing.
Qed.

Lemma CRopp_gt_lt_contravar
  : forall (R : ConstructiveReals) (r1 r2 : CRcarrier R),
    CRlt R r2 r1 -> CRlt R (CRopp R r1) (CRopp R r2).
Proof.
  intros. apply (CRplus_lt_reg_l R r1).
  destruct (CRisRing R).
  apply (CRle_lt_trans R _ (CRzero R)). apply Ropp_def.
  apply (CRplus_lt_compat_l R (CRopp R r2)) in H.
  apply (CRle_lt_trans R _ (CRplus R (CRopp R r2) r2)).
  apply (CRle_trans R _ (CRplus R r2 (CRopp R r2))).
  destruct (Ropp_def r2). exact H0.
  destruct (Radd_comm r2 (CRopp R r2)). exact H1.
  apply (CRlt_le_trans R _ _ _ H).
  destruct (Radd_comm r1 (CRopp R r2)). exact H0.
Qed.

Lemma CRopp_lt_cancel : forall (R : ConstructiveReals) (r1 r2 : CRcarrier R),
    CRlt R (CRopp R r2) (CRopp R r1) -> CRlt R r1 r2.
Proof.
  intros. apply (CRplus_lt_compat_r R r1) in H.
  destruct (CRplus_opp_l R r1) as [_ H1].
  apply (CRlt_le_trans R _ _ _ H) in H1. clear H.
  apply (CRplus_lt_compat_l R r2) in H1.
  destruct (CRplus_0_r R r2) as [_ H0].
  apply (CRlt_le_trans R _ _ _ H1) in H0. clear H1.
  destruct (Radd_assoc (CRisRing R) r2 (CRopp R r2) r1) as [H _].
  apply (CRle_lt_trans R _ _ _ H) in H0. clear H.
  apply (CRle_lt_trans R _ (CRplus R (CRzero R) r1)).
  apply (Radd_0_l (CRisRing R)).
  apply (CRle_lt_trans R _ (CRplus R (CRplus R r2 (CRopp R r2)) r1)).
  2: exact H0. apply CRplus_le_compat_r.
  destruct (Ropp_def (CRisRing R) r2). exact H.
Qed.

Lemma CRopp_plus_distr : forall (R : ConstructiveReals) (r1 r2 : CRcarrier R),
    orderEq _ (CRlt R) (CRopp R (CRplus R r1 r2)) (CRplus R (CRopp R r1) (CRopp R r2)).
Proof.
  intros. destruct (CRisRing R), (CRisRingExt R).
  apply (CRplus_eq_reg_l R (CRplus R r1 r2)).
  apply (CReq_trans R _ (CRzero R)). apply Ropp_def.
  apply (CReq_trans R _ (CRplus R (CRplus R r2 r1) (CRplus R (CRopp R r1) (CRopp R r2)))).
  apply (CReq_trans R _ (CRplus R r2 (CRplus R r1 (CRplus R (CRopp R r1) (CRopp R r2))))).
  apply (CReq_trans R _ (CRplus R r2 (CRopp R r2))).
  apply CReq_sym. apply Ropp_def. apply Radd_ext.
  apply CReq_refl.
  apply (CReq_trans R _ (CRplus R (CRzero R) (CRopp R r2))).
  apply CReq_sym, Radd_0_l.
  apply (CReq_trans R _ (CRplus R (CRplus R r1 (CRopp R r1)) (CRopp R r2))).
  apply Radd_ext. 2: apply CReq_refl. apply CReq_sym, Ropp_def.
  apply CReq_sym, Radd_assoc. apply Radd_assoc.
  apply Radd_ext. 2: apply CReq_refl. apply Radd_comm.
Qed.

Lemma CRmult_plus_distr_l : forall (R : ConstructiveReals) (r1 r2 r3 : CRcarrier R),
    orderEq _ (CRlt R) (CRmult R r1 (CRplus R r2 r3))
            (CRplus R (CRmult R r1 r2) (CRmult R r1 r3)).
Proof.
  intros. destruct (CRisRing R).
  apply (CReq_trans R _ (CRmult R (CRplus R r2 r3) r1)).
  apply Rmul_comm.
  apply (CReq_trans R _ (CRplus R (CRmult R r2 r1) (CRmult R r3 r1))).
  apply Rdistr_l.
  apply (CReq_trans R _ (CRplus R (CRmult R r1 r2) (CRmult R r3 r1))).
  destruct (CRisRingExt R). apply Radd_ext.
  apply Rmul_comm. apply CReq_refl.
  destruct (CRisRingExt R). apply Radd_ext.
  apply CReq_refl. apply Rmul_comm.
Qed.

(* x == x+x -> x == 0 *)
Lemma CRzero_double : forall (R : ConstructiveReals) (x : CRcarrier R),
    orderEq _ (CRlt R) x (CRplus R x x)
    -> orderEq _ (CRlt R) x (CRzero R).
Proof.
  intros.
  apply (CRplus_eq_reg_l R x), CReq_sym, (CReq_trans R _ x).
  apply CRplus_0_r. exact H.
Qed.

Lemma CRmult_0_r : forall (R : ConstructiveReals) (x : CRcarrier R),
    orderEq _ (CRlt R) (CRmult R x (CRzero R)) (CRzero R).
Proof.
  intros. apply CRzero_double.
  apply (CReq_trans R _ (CRmult R x (CRplus R (CRzero R) (CRzero R)))).
  destruct (CRisRingExt R). apply Rmul_ext. apply CReq_refl.
  apply CReq_sym, CRplus_0_r.
  destruct (CRisRing R). apply CRmult_plus_distr_l.
Qed.

Lemma CRopp_mult_distr_r : forall (R : ConstructiveReals) (r1 r2 : CRcarrier R),
    orderEq _ (CRlt R) (CRopp R (CRmult R r1 r2))
            (CRmult R r1 (CRopp R r2)).
Proof.
  intros. apply (CRplus_eq_reg_l R (CRmult R r1 r2)).
  destruct (CRisRing R).
  apply (CReq_trans R _ (CRzero R)). apply Ropp_def.
  apply (CReq_trans R _ (CRmult R r1 (CRplus R r2 (CRopp R r2)))).
  2: apply CRmult_plus_distr_l.
  apply (CReq_trans R _ (CRmult R r1 (CRzero R))).
  apply CReq_sym, CRmult_0_r.
  destruct (CRisRingExt R). apply Rmul_ext. apply CReq_refl.
  apply CReq_sym, Ropp_def.
Qed.

Lemma CRopp_mult_distr_l : forall (R : ConstructiveReals) (r1 r2 : CRcarrier R),
    orderEq _ (CRlt R) (CRopp R (CRmult R r1 r2))
            (CRmult R (CRopp R r1) r2).
Proof.
  intros. apply (CReq_trans R _ (CRmult R r2 (CRopp R r1))).
  apply (CReq_trans R _ (CRopp R (CRmult R r2 r1))).
  apply (Ropp_ext (CRisRingExt R)).
  apply CReq_sym, (Rmul_comm (CRisRing R)).
  apply CRopp_mult_distr_r.
  apply CReq_sym, (Rmul_comm (CRisRing R)).
Qed.

Lemma CRmult_lt_compat_r : forall (R : ConstructiveReals) (r r1 r2 : CRcarrier R),
    CRlt R (CRzero R) r
    -> CRlt R r1 r2
    -> CRlt R (CRmult R r1 r) (CRmult R r2 r).
Proof.
  intros. apply (CRplus_lt_reg_r R (CRopp R (CRmult R r1 r))).
  apply (CRle_lt_trans R _ (CRzero R)).
  apply (Ropp_def (CRisRing R)).
  apply (CRlt_le_trans R _ (CRplus R (CRmult R r2 r) (CRmult R (CRopp R r1) r))).
  apply (CRlt_le_trans R _ (CRmult R (CRplus R r2 (CRopp R r1)) r)).
  apply CRmult_lt_0_compat. 2: exact H.
  apply (CRplus_lt_reg_r R r1).
  apply (CRle_lt_trans R _ r1). apply (Radd_0_l (CRisRing R)).
  apply (CRlt_le_trans R _ r2 _ H0).
  apply (CRle_trans R _ (CRplus R r2 (CRplus R (CRopp R r1) r1))).
  apply (CRle_trans R _ (CRplus R r2 (CRzero R))).
  destruct (CRplus_0_r R r2). exact H1.
  apply CRplus_le_compat_l. destruct (CRplus_opp_l R r1). exact H1.
  destruct (Radd_assoc (CRisRing R) r2 (CRopp R r1) r1). exact H2.
  destruct (CRisRing R).
  destruct (Rdistr_l r2 (CRopp R r1) r). exact H2.
  apply CRplus_le_compat_l. destruct (CRopp_mult_distr_l R r1 r).
  exact H1.
Qed.

Lemma CRinv_r : forall (R : ConstructiveReals) (r:CRcarrier R)
                  (rnz : orderAppart _ (CRlt R) r (CRzero R)),
    orderEq _ (CRlt R) (CRmult R r (CRinv R r rnz)) (CRone R).
Proof.
  intros. apply (CReq_trans R _ (CRmult R (CRinv R r rnz) r)).
  apply (CRisRing R). apply CRinv_l.
Qed.

Lemma CRmult_lt_reg_r : forall (R : ConstructiveReals) (r r1 r2 : CRcarrier R),
    CRlt R (CRzero R) r
    -> CRlt R (CRmult R r1 r) (CRmult R r2 r)
    -> CRlt R r1 r2.
Proof.
  intros. apply (CRmult_lt_compat_r R (CRinv R r (inr H))) in H0.
  2: apply CRinv_0_lt_compat, H.
  apply (CRle_lt_trans R _ (CRmult R (CRmult R r1 r) (CRinv R r (inr H)))).
  - clear H0. apply (CRle_trans R _ (CRmult R r1 (CRone R))).
    destruct (CRmult_1_r R r1). exact H0.
    apply (CRle_trans R _ (CRmult R r1 (CRmult R r (CRinv R r (inr H))))).
    destruct (Rmul_ext (CRisRingExt R) r1 r1 (CReq_refl R r1)
                       (CRmult R r (CRinv R r (inr H))) (CRone R)).
    apply CRinv_r. exact H0.
    destruct (Rmul_assoc (CRisRing R) r1 r (CRinv R r (inr H))). exact H1.
  - apply (CRlt_le_trans R _ (CRmult R (CRmult R r2 r) (CRinv R r (inr H)))).
    exact H0. clear H0.
    apply (CRle_trans R _ (CRmult R r2 (CRone R))).
    2: destruct (CRmult_1_r R r2); exact H1.
    apply (CRle_trans R _ (CRmult R r2 (CRmult R r (CRinv R r (inr H))))).
    destruct (Rmul_assoc (CRisRing R) r2 r (CRinv R r (inr H))). exact H0.
    destruct (Rmul_ext (CRisRingExt R) r2 r2 (CReq_refl R r2)
                       (CRmult R r (CRinv R r (inr H))) (CRone R)).
    apply CRinv_r. exact H1.
Qed.

Lemma CRmult_lt_reg_l : forall (R : ConstructiveReals) (r r1 r2 : CRcarrier R),
    CRlt R (CRzero R) r
    -> CRlt R (CRmult R r r1) (CRmult R r r2)
    -> CRlt R r1 r2.
Proof.
  intros.
  destruct (Rmul_comm (CRisRing R) r r1) as [H1 _].
  apply (CRle_lt_trans R _ _ _ H1) in H0. clear H1.
  destruct (Rmul_comm (CRisRing R) r r2) as [_ H1].
  apply (CRlt_le_trans R _ _ _ H0) in H1. clear H0.
  apply CRmult_lt_reg_r in H1.
  exact H1. exact H.
Qed.

Lemma CRmult_le_compat_l : forall (R : ConstructiveReals) (r r1 r2 : CRcarrier R),
    CRlt R (CRzero R) r
    -> orderLe _ (CRlt R) r1 r2
    -> orderLe _ (CRlt R) (CRmult R r r1) (CRmult R r r2).
Proof.
  intros. intro abs. apply CRmult_lt_reg_l in abs.
  contradiction. exact H.
Qed.

Lemma CRmult_le_compat_r : forall (R : ConstructiveReals) (r r1 r2 : CRcarrier R),
    CRlt R (CRzero R) r
    -> orderLe _ (CRlt R) r1 r2
    -> orderLe _ (CRlt R) (CRmult R r1 r) (CRmult R r2 r).
Proof.
  intros. intro abs. apply CRmult_lt_reg_r in abs.
  contradiction. exact H.
Qed.

Lemma CRmult_eq_reg_r : forall (R : ConstructiveReals) (r r1 r2 : CRcarrier R),
    orderAppart _ (CRlt R) (CRzero R) r
    -> orderEq _ (CRlt R) (CRmult R r1 r) (CRmult R r2 r)
    -> orderEq _ (CRlt R) r1 r2.
Proof.
  intros. destruct H0,H.
  - split.
    + intro abs. apply H0. apply CRmult_lt_compat_r.
      exact c. exact abs.
    + intro abs. apply H1. apply CRmult_lt_compat_r.
      exact c. exact abs.
  - split.
    + intro abs. apply H1. apply CRopp_lt_cancel.
      apply (CRle_lt_trans R _ (CRmult R r1 (CRopp R r))).
      apply CRopp_mult_distr_r.
      apply (CRlt_le_trans R _ (CRmult R r2 (CRopp R r))).
      2: apply CRopp_mult_distr_r.
      apply CRmult_lt_compat_r. 2: exact abs.
      apply (CRplus_lt_reg_r R r). apply (CRle_lt_trans R _ r).
      apply (Radd_0_l (CRisRing R)).
      apply (CRlt_le_trans R _ (CRzero R) _ c).
      apply CRplus_opp_l.
    + intro abs. apply H0. apply CRopp_lt_cancel.
      apply (CRle_lt_trans R _ (CRmult R r2 (CRopp R r))).
      apply CRopp_mult_distr_r.
      apply (CRlt_le_trans R _ (CRmult R r1 (CRopp R r))).
      2: apply CRopp_mult_distr_r.
      apply CRmult_lt_compat_r. 2: exact abs.
      apply (CRplus_lt_reg_r R r). apply (CRle_lt_trans R _ r).
      apply (Radd_0_l (CRisRing R)).
      apply (CRlt_le_trans R _ (CRzero R) _ c).
      apply CRplus_opp_l.
Qed.

Lemma CR_of_Q_proper : forall (R : ConstructiveReals) (q r : Q),
    q == r -> orderEq _ (CRlt R) (CR_of_Q R q) (CR_of_Q R r).
Proof.
  split.
  - intro abs. apply lt_CR_of_Q in abs. rewrite H in abs.
    exact (Qlt_not_le r r abs (Qle_refl r)).
  - intro abs. apply lt_CR_of_Q in abs. rewrite H in abs.
    exact (Qlt_not_le r r abs (Qle_refl r)).
Qed.

Lemma CR_of_Q_zero : forall (R : ConstructiveReals),
    orderEq _ (CRlt R) (CR_of_Q R 0) (CRzero R).
Proof.
  intros. apply CRzero_double.
  apply (CReq_trans R _ (CR_of_Q R (0+0))). apply CR_of_Q_proper.
  reflexivity. apply CR_of_Q_plus.
Qed.

Lemma CR_of_Q_opp : forall (R : ConstructiveReals) (q : Q),
    orderEq _ (CRlt R) (CR_of_Q R (-q)) (CRopp R (CR_of_Q R q)).
Proof.
  intros. apply (CRplus_eq_reg_l R (CR_of_Q R q)).
  apply (CReq_trans R _ (CRzero R)).
  apply (CReq_trans R _ (CR_of_Q R (q-q))).
  apply CReq_sym, CR_of_Q_plus.
  apply (CReq_trans R _ (CR_of_Q R 0)).
  apply CR_of_Q_proper. ring. apply CR_of_Q_zero.
  apply CReq_sym. apply (CRisRing R).
Qed.

Lemma CR_of_Q_le : forall (R : ConstructiveReals) (r q : Q),
    Qle r q
    -> orderLe _ (CRlt R) (CR_of_Q R r) (CR_of_Q R q).
Proof.
  intros. intro abs. apply lt_CR_of_Q in abs.
  exact (Qlt_not_le _ _ abs H).
Qed.

Lemma CR_of_Q_pos : forall (R : ConstructiveReals) (q:Q),
    Qlt 0 q -> CRlt R (CRzero R) (CR_of_Q R q).
Proof.
  intros. apply (CRle_lt_trans R _ (CR_of_Q R 0)).
  apply CR_of_Q_zero. apply CR_of_Q_lt. exact H.
Qed.

Lemma CR_cv_above_rat
  : forall (R : ConstructiveReals) (xn : nat -> Q) (x : CRcarrier R) (q : Q),
    CR_cv R (fun n : nat => CR_of_Q R (xn n)) x
    -> CRlt R (CR_of_Q R q) x
    -> { n : nat | forall p:nat, le n p -> Qlt q (xn p) }.
Proof.
  intros.
  destruct (CR_Q_dense R _ _ H0) as [r [H1 H2]].
  apply lt_CR_of_Q in H1. clear H0.
  destruct (Qarchimedean (/(r-q))) as [p pmaj].
  destruct (H p) as [n nmaj].
  exists n. intros k lenk. specialize (nmaj k lenk) as [H3 _].
  apply (lt_CR_of_Q R), (CRlt_le_trans R _ (CRplus R x (CR_of_Q R (-1#p)))).
  apply (CRlt_trans R _ (CRplus R (CR_of_Q R r) (CR_of_Q R (-1#p)))).
  2: apply CRplus_lt_compat_r, H2.
  apply (CRlt_le_trans R _ (CR_of_Q R (r+(-1#p)))).
  - apply CR_of_Q_lt.
    apply (Qplus_lt_l _ _ (-(-1#p)-q)). field_simplify.
    setoid_replace (-1*(-1#p)) with (1#p). 2: reflexivity.
    apply (Qmult_lt_l _ _ (r-q)) in pmaj.
    rewrite Qmult_inv_r in pmaj. apply Qlt_shift_div_r in pmaj.
    2: reflexivity. setoid_replace (-1*q + r) with (r-q). exact pmaj.
    ring. intro abs. apply Qlt_minus_iff in H1.
    rewrite abs in H1. inversion H1.
    apply Qlt_minus_iff in H1. exact H1.
  - apply CR_of_Q_plus.
  - apply (CRplus_le_reg_r R (CRopp R x)).
    apply (CRle_trans R _ (CR_of_Q R (-1#p))). 2: exact H3. clear H3.
    apply (CRle_trans R _ (CRplus R (CRopp R x) (CRplus R x (CR_of_Q R (-1 # p))))).
    exact (proj1 (Radd_comm (CRisRing R) _ _)).
    apply (CRle_trans R _ (CRplus R (CRplus R (CRopp R x) x) (CR_of_Q R (-1 # p)))).
    exact (proj2 (Radd_assoc (CRisRing R) _ _ _)).
    apply (CRle_trans R _ (CRplus R (CRzero R) (CR_of_Q R (-1 # p)))).
    apply CRplus_le_compat_r. exact (proj2 (CRplus_opp_l R _)).
    exact (proj2 (Radd_0_l (CRisRing R) _)).
Qed.

Lemma CR_cv_below_rat
  : forall (R : ConstructiveReals) (xn : nat -> Q) (x : CRcarrier R) (q : Q),
    CR_cv R (fun n : nat => CR_of_Q R (xn n)) x
    -> CRlt R x (CR_of_Q R q)
    -> { n : nat | forall p:nat, le n p -> Qlt (xn p) q }.
Proof.
  intros.
  destruct (CR_Q_dense R _ _ H0) as [r [H1 H2]].
  apply lt_CR_of_Q in H2. clear H0.
  destruct (Qarchimedean (/(q-r))) as [p pmaj].
  destruct (H p) as [n nmaj].
  exists n. intros k lenk. specialize (nmaj k lenk) as [_ H4].
  apply (lt_CR_of_Q R), (CRle_lt_trans R _ (CRplus R x (CR_of_Q R (1#p)))).
  - apply (CRplus_le_reg_r R (CRopp R x)).
    apply (CRle_trans R _ (CR_of_Q R (1#p))). exact H4. clear H4.
    apply (CRle_trans R _ (CRplus R (CRopp R x) (CRplus R x (CR_of_Q R (1 # p))))).
    2: exact (proj1 (Radd_comm (CRisRing R) _ _)).
    apply (CRle_trans R _ (CRplus R (CRplus R (CRopp R x) x) (CR_of_Q R (1 # p)))).
    2: exact (proj1 (Radd_assoc (CRisRing R) _ _ _)).
    apply (CRle_trans R _ (CRplus R (CRzero R) (CR_of_Q R (1 # p)))).
    exact (proj1 (Radd_0_l (CRisRing R) _)).
    apply CRplus_le_compat_r. exact (proj1 (CRplus_opp_l R _)).
  - apply (CRlt_trans R _ (CRplus R (CR_of_Q R r) (CR_of_Q R (1 # p)))).
    apply CRplus_lt_compat_r. exact H1.
    apply (CRle_lt_trans R _ (CR_of_Q R (r + (1#p)))).
    apply CR_of_Q_plus. apply CR_of_Q_lt.
    apply (Qmult_lt_l _ _ (q-r)) in pmaj.
    rewrite Qmult_inv_r in pmaj. apply Qlt_shift_div_r in pmaj.
    apply (Qplus_lt_l _ _ (-r)). field_simplify.
    setoid_replace (-1*r + q) with (q-r). exact pmaj.
    ring. reflexivity. intro abs. apply Qlt_minus_iff in H2.
    rewrite abs in H2. inversion H2.
    apply Qlt_minus_iff in H2. exact H2.
Qed.

Lemma CR_cv_const : forall (R : ConstructiveReals) (x y : CRcarrier R),
    CR_cv R (fun _ => x) y -> orderEq _ (CRlt R) x y.
Proof.
  intros. destruct (CRisRing R). split.
  - intro abs.
    destruct (CR_Q_dense R x y abs) as [q [H0 H1]].
    destruct (CR_Q_dense R _ _ H1) as [r [H2 H3]].
    apply lt_CR_of_Q in H2.
    destruct (Qarchimedean (/(r-q))) as [p pmaj].
    destruct (H p) as [n nmaj]. specialize (nmaj n (le_refl n)) as [nmaj _].
    apply nmaj. clear nmaj.
    apply (CRlt_trans R _ (CR_of_Q R (q-r))).
    apply (CRlt_le_trans R _ (CRplus R (CR_of_Q R q) (CRopp R (CR_of_Q R r)))).
    + apply CRplus_lt_le_compat. exact H0.
      intro H4. apply CRopp_lt_cancel in H4. exact (CRlt_asym R _ _ H4 H3).
    + apply (CRle_trans R _ (CRplus R (CR_of_Q R q) (CR_of_Q R (-r)))).
      apply CRplus_le_compat_l. exact (proj1 (CR_of_Q_opp R r)).
      exact (proj1 (CR_of_Q_plus R _ _)).
    + apply CR_of_Q_lt.
      apply (Qplus_lt_l _ _ (-(-1#p)+r-q)). field_simplify.
      setoid_replace (-1*(-1#p)) with (1#p). 2: reflexivity.
      apply (Qmult_lt_l _ _ (r-q)) in pmaj.
      rewrite Qmult_inv_r in pmaj. apply Qlt_shift_div_r in pmaj.
      2: reflexivity. setoid_replace (-1*q + r) with (r-q). exact pmaj.
      ring. intro H4. apply Qlt_minus_iff in H2.
      rewrite H4 in H2. inversion H2.
      apply Qlt_minus_iff in H2. exact H2.
  - intro abs.
    destruct (CR_Q_dense R _ _ abs) as [q [H0 H1]].
    destruct (CR_Q_dense R _ _ H0) as [r [H2 H3]].
    apply lt_CR_of_Q in H3.
    destruct (Qarchimedean (/(q-r))) as [p pmaj].
    destruct (H p) as [n nmaj]. specialize (nmaj n (le_refl n)) as [_ nmaj].
    apply nmaj. clear nmaj.
    apply (CRlt_trans R _ (CR_of_Q R (q-r))).
    + apply CR_of_Q_lt.
      apply (Qmult_lt_l _ _ (q-r)) in pmaj.
      rewrite Qmult_inv_r in pmaj. apply Qlt_shift_div_r in pmaj.
      exact pmaj. reflexivity.
      intro H4. apply Qlt_minus_iff in H3.
      rewrite H4 in H3. inversion H3.
      apply Qlt_minus_iff in H3. exact H3.
    + apply (CRle_lt_trans R _ (CRplus R (CR_of_Q R q) (CR_of_Q R (-r)))).
      apply CR_of_Q_plus.
      apply (CRle_lt_trans R _ (CRplus R (CR_of_Q R q) (CRopp R (CR_of_Q R r)))).
      apply CRplus_le_compat_l. exact (proj2 (CR_of_Q_opp R r)).
      apply CRplus_lt_le_compat. exact H1.
      intro H4. apply CRopp_lt_cancel in H4.
      exact (CRlt_asym R _ _ H4 H2).
Qed.
