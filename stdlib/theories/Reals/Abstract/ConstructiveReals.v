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

(** An interface for constructive and computable real numbers.
    All of its instances are isomorphic (see file ConstructiveRealsMorphisms).
    For example it is implemented by the Cauchy reals in file
    ConstructivecauchyReals and also implemented by the sumbool-based
    Dedekind reals defined by

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

  Any computation about constructive reals can be worked
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
  will yield fast and small extracted programs.

  Constructive reals are setoids, which custom equality is defined as
  x == y  iff  (x <= y /\ y <= x).
  It is hard to quotient constructively to get the Leibniz equality
  on the real numbers. In "Sheaves in Geometry and Logic",
  MacLane and Moerdijk show a topos in which all functions R -> Z
  are constant. Consequently all functions R -> Q are constant and
  it is not possible to approximate real numbers by rational numbers.

  WARNING: this file is experimental and likely to change in future releases.
 *)


Require Import QArith Qabs Qround.

Definition isLinearOrder {X : Set} (Xlt : X -> X -> Set) : Set
  := (forall x y:X, Xlt x y -> Xlt y x -> False)
     * (forall x y z : X, Xlt x y -> Xlt y z -> Xlt x z)
     * (forall x y z : X, Xlt x z -> Xlt x y + Xlt y z).

Structure ConstructiveReals : Type :=
  {
    CRcarrier : Set;

    (* Put this order relation in sort Set rather than Prop,
       to allow the definition of fast ConstructiveReals morphisms.
       For example, the Cauchy reals do store information in
       the proofs of CRlt, which is used in algorithms in sort Set. *)
    CRlt : CRcarrier -> CRcarrier -> Set;
    CRltLinear : isLinearOrder CRlt;

    CRle (x y : CRcarrier) := CRlt y x -> False;
    CReq (x y : CRcarrier) := CRle y x /\ CRle x y;
    CRapart (x y : CRcarrier) := sum (CRlt x y) (CRlt y x);

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

    (* The initial field morphism (in characteristic zero).
       The abstract definition by iteration of addition is
       probably the slowest. Let each instance implement
       a faster (and often simpler) version. *)
    CR_of_Q : Q -> CRcarrier;
    CR_of_Q_lt : forall q r : Q,
        Qlt q r -> CRlt (CR_of_Q q) (CR_of_Q r);
    lt_CR_of_Q : forall q r : Q,
        CRlt (CR_of_Q q) (CR_of_Q r) -> Qlt q r;

    (* Addition and multiplication *)
    CRplus : CRcarrier -> CRcarrier -> CRcarrier;
    CRopp : CRcarrier -> CRcarrier; (* Computable opposite,
                         stronger than Prop-existence of opposite *)
    CRmult : CRcarrier -> CRcarrier -> CRcarrier;

    CR_of_Q_plus : forall q r : Q, CReq (CR_of_Q (q+r))
                                           (CRplus (CR_of_Q q) (CR_of_Q r));
    CR_of_Q_mult : forall q r : Q, CReq (CR_of_Q (q*r))
                                           (CRmult (CR_of_Q q) (CR_of_Q r));
    CRisRing : ring_theory (CR_of_Q 0) (CR_of_Q 1) CRplus CRmult
                          (fun x y => CRplus x (CRopp y)) CRopp CReq;
    CRisRingExt : ring_eq_ext CRplus CRmult CRopp CReq;

    (* Compatibility with order *)
    CRzero_lt_one : CRlt (CR_of_Q 0) (CR_of_Q 1);
    CRplus_lt_compat_l : forall r r1 r2 : CRcarrier,
        CRlt r1 r2 -> CRlt (CRplus r r1) (CRplus r r2);
    CRplus_lt_reg_l : forall r r1 r2 : CRcarrier,
        CRlt (CRplus r r1) (CRplus r r2) -> CRlt r1 r2;
    CRmult_lt_0_compat : forall x y : CRcarrier,
        CRlt (CR_of_Q 0) x -> CRlt (CR_of_Q 0) y -> CRlt (CR_of_Q 0) (CRmult x y);

    (* A constructive total inverse function on F would need to be continuous,
       which is impossible because we cannot connect plus and minus infinities.
       Therefore it has to be a partial function, defined on non zero elements.
       For this reason we cannot use Coq's field_theory and field tactic.

       To implement Finv by Cauchy sequences we need orderAppart,
       ~orderEq is not enough. *)
    CRinv : forall x : CRcarrier, CRapart x (CR_of_Q 0) -> CRcarrier;
    CRinv_l : forall (r:CRcarrier) (rnz : CRapart r (CR_of_Q 0)),
        CReq (CRmult (CRinv r rnz) r) (CR_of_Q 1);
    CRinv_0_lt_compat : forall (r : CRcarrier) (rnz : CRapart r (CR_of_Q 0)),
        CRlt (CR_of_Q 0) r -> CRlt (CR_of_Q 0) (CRinv r rnz);

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

    (* Absolute value, CRabs x is the least upper bound
       of the pair x, -x. *)
    CRabs : CRcarrier -> CRcarrier;
    CRabs_def : forall x y : CRcarrier,
        (CRle x y /\ CRle (CRopp x) y)
        <-> CRle (CRabs x) y;

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
                           -> CRle (CRabs (CRminus (un i) l))
                                  (CR_of_Q (1#p)) };
    CR_cauchy (un : nat -> CRcarrier) : Set
    := forall p : positive,
        { n : nat  |  forall i j:nat, le n i -> le n j
                             -> CRle (CRabs (CRminus (un i) (un j)))
                                    (CR_of_Q (1#p)) };

    (* For the Cauchy reals, this algorithm consists in building
       a Cauchy sequence of rationals un : nat -> Q that has
       the same limit as xn. For each n:nat, un n is a 1/n
       rational approximation of a point of xn that has converged
       within 1/n. *)
    CR_complete :
      forall xn : (nat -> CRcarrier),
        CR_cauchy xn -> { l : CRcarrier  &  CR_cv xn l };
  }.

Declare Scope ConstructiveReals.

Delimit Scope ConstructiveReals with ConstructiveReals.

Notation "x < y" := (CRlt _ x y) : ConstructiveReals.
Notation "x <= y" := (CRle _ x y) : ConstructiveReals.
Notation "x <= y <= z" := (CRle _ x y /\ CRle _ y z) : ConstructiveReals.
Notation "x < y < z"   := (prod (CRlt _ x y) (CRlt _ y z)) : ConstructiveReals.
Notation "x == y" := (CReq _ x y) : ConstructiveReals.
Notation "x ≶ y" := (CRapart _ x y) (at level 70, no associativity) : ConstructiveReals.
Notation "0" := (CR_of_Q _ 0) : ConstructiveReals.
Notation "1" := (CR_of_Q _ 1) : ConstructiveReals.
Notation "2" := (CR_of_Q _ 2) : ConstructiveReals.
Notation "3" := (CR_of_Q _ 3) : ConstructiveReals.
Notation "4" := (CR_of_Q _ 4) : ConstructiveReals.
Notation "5" := (CR_of_Q _ 5) : ConstructiveReals.
Notation "6" := (CR_of_Q _ 6) : ConstructiveReals.
Notation "7" := (CR_of_Q _ 7) : ConstructiveReals.
Notation "8" := (CR_of_Q _ 8) : ConstructiveReals.
Notation "9" := (CR_of_Q _ 9) : ConstructiveReals.
Notation "10" := (CR_of_Q _ 10) : ConstructiveReals.
Notation "x + y" := (CRplus _ x y) : ConstructiveReals.
Notation "- x" := (CRopp _ x) : ConstructiveReals.
Notation "x - y" := (CRminus _ x y) : ConstructiveReals.
Notation "x * y" := (CRmult _ x y) : ConstructiveReals.
Notation "/ x" := (CRinv _ x)  : ConstructiveReals.

Local Open Scope ConstructiveReals.

Lemma CRlt_asym : forall {R : ConstructiveReals} (x y : CRcarrier R),
    x < y -> x <= y.
Proof.
  intros. intro H0. destruct (CRltLinear R), p.
  apply (f x y); assumption.
Qed.

Lemma CRlt_proper
  : forall R : ConstructiveReals,
    CMorphisms.Proper
      (CMorphisms.respectful (CReq R)
                             (CMorphisms.respectful (CReq R) CRelationClasses.iffT)) (CRlt R).
Proof.
  intros R x y H x0 y0 H0. destruct H, H0.
  destruct (CRltLinear R). split.
  - intro. destruct (s x y x0).
    + assumption.
    + contradiction.
    + destruct (s y y0 x0).
      * assumption.
      * assumption.
      * contradiction.
  - intro. destruct (s y x y0).
    + assumption.
    + contradiction.
    + destruct (s x x0 y0).
      * assumption.
      * assumption.
      * contradiction.
Qed.

Lemma CRle_refl : forall {R : ConstructiveReals} (x : CRcarrier R),
    x <= x.
Proof.
  intros. intro H. destruct (CRltLinear R), p.
  exact (f x x H H).
Qed.

Lemma CRle_lt_trans : forall {R : ConstructiveReals} (r1 r2 r3 : CRcarrier R),
    r1 <= r2 -> r2 < r3 -> r1 < r3.
Proof.
  intros. destruct (CRltLinear R).
  destruct (s r2 r1 r3 H0).
  - contradiction.
  - apply c.
Qed.

Lemma CRlt_le_trans : forall {R : ConstructiveReals} (r1 r2 r3 : CRcarrier R),
    r1 < r2 -> r2 <= r3 -> r1 < r3.
Proof.
  intros. destruct (CRltLinear R).
  destruct (s r1 r3 r2 H).
  - apply c.
  - contradiction.
Qed.

Lemma CRle_trans : forall {R : ConstructiveReals} (x y z : CRcarrier R),
    x <= y -> y <= z -> x <= z.
Proof.
  intros. intro abs. apply H0.
  apply (CRlt_le_trans _ x); assumption.
Qed.

Lemma CRlt_trans : forall {R : ConstructiveReals} (x y z : CRcarrier R),
    x < y -> y < z -> x < z.
Proof.
  intros. apply (CRlt_le_trans _ y _ H).
  apply CRlt_asym. exact H0.
Qed.

Lemma CRlt_trans_flip : forall {R : ConstructiveReals} (x y z : CRcarrier R),
    y < z -> x < y -> x < z.
Proof.
  intros. apply (CRlt_le_trans _ y).
  - exact H0.
  - apply CRlt_asym. exact H.
Qed.

Lemma CReq_refl : forall {R : ConstructiveReals} (x : CRcarrier R),
    x == x.
Proof.
  split; apply CRle_refl.
Qed.

Lemma CReq_sym : forall {R : ConstructiveReals} (x y : CRcarrier R),
    x == y -> y == x.
Proof.
  intros. destruct H. split; intro abs; contradiction.
Qed.

Lemma CReq_trans : forall {R : ConstructiveReals} (x y z : CRcarrier R),
    x == y -> y == z -> x == z.
Proof.
  intros. destruct H,H0. destruct (CRltLinear R), p. split.
  - intro abs. destruct (s _ y _ abs); contradiction.
  - intro abs. destruct (s _ y _ abs); contradiction.
Qed.

Add Parametric Relation {R : ConstructiveReals} : (CRcarrier R) (CReq R)
    reflexivity proved by (CReq_refl)
    symmetry proved by (CReq_sym)
    transitivity proved by (CReq_trans)
      as CReq_rel.

#[global]
Instance CReq_relT : forall {R : ConstructiveReals},
    CRelationClasses.Equivalence (CReq R).
Proof.
  split.
  - exact CReq_refl.
  - exact CReq_sym.
  - exact CReq_trans.
Qed.

#[global]
Instance CRlt_morph
  : forall {R : ConstructiveReals}, CMorphisms.Proper
      (CMorphisms.respectful (CReq R) (CMorphisms.respectful (CReq R) CRelationClasses.iffT)) (CRlt R).
Proof.
  intros R x y H x0 y0 H0. destruct H, H0. split.
  - intro. destruct (CRltLinear R). destruct (s x y x0).
    + assumption.
    + contradiction.
    + destruct (s y y0 x0).
      * assumption.
      * assumption.
      * contradiction.
  - intro. destruct (CRltLinear R). destruct (s y x y0).
    + assumption.
    + contradiction.
    + destruct (s x x0 y0).
      * assumption.
      * assumption.
      * contradiction.
Qed.

Add Parametric Morphism {R : ConstructiveReals} : (CRle R)
    with signature CReq R ==> CReq R ==> iff
      as CRle_morph.
Proof.
  intros. split.
  - intros H1 H2. unfold CRle in H1.
    rewrite <- H0 in H2. rewrite <- H in H2. contradiction.
  - intros H1 H2. unfold CRle in H1.
    rewrite H0 in H2. rewrite H in H2. contradiction.
Qed.

Lemma CRplus_0_l : forall {R : ConstructiveReals} (x : CRcarrier R),
    0 + x == x.
Proof.
  intros. destruct (CRisRing R). apply Radd_0_l.
Qed.

Lemma CRplus_0_r : forall {R : ConstructiveReals} (x : CRcarrier R),
    x + 0 == x.
Proof.
  intros. destruct (CRisRing R).
  transitivity (0 + x).
  - apply Radd_comm.
  - apply Radd_0_l.
Qed.

Lemma CRplus_opp_l : forall {R : ConstructiveReals} (x : CRcarrier R),
    - x + x == 0.
Proof.
  intros. destruct (CRisRing R).
  transitivity (x + - x).
  - apply Radd_comm.
  - apply Ropp_def.
Qed.

Lemma CRplus_opp_r : forall {R : ConstructiveReals} (x : CRcarrier R),
    x + - x == 0.
Proof.
  intros. destruct (CRisRing R). apply Ropp_def.
Qed.

Lemma CRopp_0 : forall {R : ConstructiveReals},
    CRopp R 0 == 0.
Proof.
  intros. rewrite <- CRplus_0_r, CRplus_opp_l.
  reflexivity.
Qed.

Lemma CRplus_lt_compat_r : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    r1 < r2 -> r1 + r < r2 + r.
Proof.
  intros. destruct (CRisRing R).
  apply (CRlt_proper R (CRplus R r r1) (CRplus R r1 r) (Radd_comm _ _)
                     (CRplus R r2 r) (CRplus R r2 r)).
  - apply CReq_refl.
  - apply (CRlt_proper R _ _ (CReq_refl _) _ (CRplus R r r2)).
    + apply Radd_comm.
    + apply CRplus_lt_compat_l. exact H.
Qed.

Lemma CRplus_lt_reg_r : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    r1 + r < r2 + r -> r1 < r2.
Proof.
  intros. destruct (CRisRing R).
  apply (CRlt_proper R (CRplus R r r1) (CRplus R r1 r) (Radd_comm _ _)
                     (CRplus R r2 r) (CRplus R r2 r)) in H.
  2: apply CReq_refl.
  apply (CRlt_proper R _ _ (CReq_refl _) _ (CRplus R r r2)) in H.
  - apply CRplus_lt_reg_l in H. exact H.
  - apply Radd_comm.
Qed.

Lemma CRplus_le_compat_l : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    r1 <= r2 -> r + r1 <= r + r2.
Proof.
  intros. intros abs. apply CRplus_lt_reg_l in abs. apply H. exact abs.
Qed.

Lemma CRplus_le_compat_r : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    r1 <= r2 -> r1 + r <= r2 + r.
Proof.
  intros. intros abs. apply CRplus_lt_reg_r in abs. apply H. exact abs.
Qed.

Lemma CRplus_le_compat : forall {R : ConstructiveReals} (r1 r2 r3 r4 : CRcarrier R),
    r1 <= r2 -> r3 <= r4 -> r1 + r3 <= r2 + r4.
Proof.
  intros. apply (CRle_trans _ (CRplus R r2 r3)).
  - apply CRplus_le_compat_r, H.
  - apply CRplus_le_compat_l, H0.
Qed.

Lemma CRle_minus : forall {R : ConstructiveReals} (x y : CRcarrier R),
    x <= y -> 0 <= y - x.
Proof.
  intros. rewrite <- (CRplus_opp_r x).
  apply CRplus_le_compat_r. exact H.
Qed.

Lemma CRplus_le_reg_l : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    r + r1 <= r + r2 -> r1 <= r2.
Proof.
  intros. intro abs. apply H. clear H.
  apply CRplus_lt_compat_l. exact abs.
Qed.

Lemma CRplus_le_reg_r : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    r1 + r <= r2 + r -> r1 <= r2.
Proof.
  intros. intro abs. apply H. clear H.
  apply CRplus_lt_compat_r. exact abs.
Qed.

Lemma CRplus_lt_le_compat :
  forall {R : ConstructiveReals} (r1 r2 r3 r4 : CRcarrier R),
    r1 < r2
    -> r3 <= r4
    -> r1 + r3 < r2 + r4.
Proof.
  intros. apply (CRlt_le_trans _ (CRplus R r2 r3)).
  - apply CRplus_lt_compat_r. exact H.
  - intro abs.
    apply CRplus_lt_reg_l in abs. contradiction.
Qed.

Lemma CRplus_le_lt_compat :
  forall {R : ConstructiveReals} (r1 r2 r3 r4 : CRcarrier R),
    r1 <= r2
    -> r3 < r4
    -> r1 + r3 < r2 + r4.
Proof.
  intros. apply (CRle_lt_trans _ (CRplus R r2 r3)).
  - apply CRplus_le_compat_r. exact H.
  - apply CRplus_lt_compat_l. exact H0.
Qed.

Lemma CRplus_eq_reg_l : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    r + r1 == r + r2 -> r1 == r2.
Proof.
  intros.
  destruct (CRisRingExt R). clear Rmul_ext Ropp_ext.
  pose proof (Radd_ext
                (CRopp R r) (CRopp R r) (CReq_refl _)
                _ _ H).
  destruct (CRisRing R).
  apply (CReq_trans r1) in H0.
  - apply (CReq_trans _ _ _ H0).
    transitivity ((- r + r) + r2).
    + apply Radd_assoc.
    + transitivity (0 + r2).
      * apply Radd_ext.
        -- apply CRplus_opp_l.
        -- apply CReq_refl.
      * apply Radd_0_l.
  - apply CReq_sym.
    transitivity (- r + r + r1).
    + apply Radd_assoc.
    + transitivity (0 + r1).
      * apply Radd_ext.
        -- apply CRplus_opp_l.
        -- apply CReq_refl.
      * apply Radd_0_l.
Qed.

Lemma CRplus_eq_reg_r : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    r1 + r == r2 + r -> r1 == r2.
Proof.
  intros. apply (CRplus_eq_reg_l r).
  transitivity (r1 + r).
  - apply (Radd_comm (CRisRing R)).
  - transitivity (r2 + r).
    + exact H.
    + apply (Radd_comm (CRisRing R)).
Qed.

Lemma CRplus_assoc : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    r + r1 + r2 == r + (r1 + r2).
Proof.
  intros. symmetry. apply (Radd_assoc (CRisRing R)).
Qed.

Lemma CRplus_comm : forall {R : ConstructiveReals} (r1 r2 : CRcarrier R),
    r1 + r2 == r2 + r1.
Proof.
  intros. apply (Radd_comm (CRisRing R)).
Qed.

Add Parametric Morphism {R : ConstructiveReals} : (CRplus R)
    with signature CReq R ==> CReq R ==> CReq R
      as CRplus_morph.
Proof.
  apply (CRisRingExt R).
Qed.

Add Parametric Morphism {R : ConstructiveReals} : (CRopp R)
    with signature CReq R ==> CReq R
      as CRopp_morph.
Proof.
  apply (CRisRingExt R).
Qed.

Add Parametric Morphism {R : ConstructiveReals} : (CRmult R)
    with signature CReq R ==> CReq R ==> CReq R
      as CRmult_morph.
Proof.
  apply (CRisRingExt R).
Qed.

#[global]
Instance CRplus_morph_T
  : forall {R : ConstructiveReals}, CMorphisms.Proper
      (CMorphisms.respectful (CReq R) (CMorphisms.respectful (CReq R) (CReq R))) (CRplus R).
Proof.
  intros R x y H z t H1. apply CRplus_morph; assumption.
Qed.

#[global]
Instance CRmult_morph_T
  : forall {R : ConstructiveReals}, CMorphisms.Proper
      (CMorphisms.respectful (CReq R) (CMorphisms.respectful (CReq R) (CReq R))) (CRmult R).
Proof.
  intros R x y H z t H1. apply CRmult_morph; assumption.
Qed.

#[global]
Instance CRopp_morph_T
  : forall {R : ConstructiveReals}, CMorphisms.Proper
      (CMorphisms.respectful (CReq R) (CReq R)) (CRopp R).
Proof.
  apply CRisRingExt.
Qed.

Add Parametric Morphism {R : ConstructiveReals} : (CRminus R)
    with signature (CReq R) ==> (CReq R) ==> (CReq R)
      as CRminus_morph.
Proof.
  intros. unfold CRminus. rewrite H,H0. reflexivity.
Qed.

#[global]
Instance CRminus_morph_T
  : forall {R : ConstructiveReals}, CMorphisms.Proper
      (CMorphisms.respectful (CReq R) (CMorphisms.respectful (CReq R) (CReq R))) (CRminus R).
Proof.
  intros R x y exy z t ezt. unfold CRminus. rewrite exy,ezt. reflexivity.
Qed.

Lemma CRopp_involutive : forall {R : ConstructiveReals} (r : CRcarrier R),
    - - r == r.
Proof.
  intros. apply (CRplus_eq_reg_l (CRopp R r)).
  transitivity (CR_of_Q R 0).
  - apply CRisRing.
  - apply CReq_sym. transitivity (r + - r).
    + apply CRisRing.
    + apply CRisRing.
Qed.

Lemma CRopp_gt_lt_contravar
  : forall {R : ConstructiveReals} (r1 r2 : CRcarrier R),
    r2 < r1 -> - r1 < - r2.
Proof.
  intros. apply (CRplus_lt_reg_l R r1).
  destruct (CRisRing R).
  apply (CRle_lt_trans _ 0).
  - apply Ropp_def.
  - apply (CRplus_lt_compat_l R (CRopp R r2)) in H.
    apply (CRle_lt_trans _ (CRplus R (CRopp R r2) r2)).
    + apply (CRle_trans _ (CRplus R r2 (CRopp R r2))).
      * destruct (Ropp_def r2). exact H0.
      * destruct (Radd_comm r2 (CRopp R r2)). exact H1.
    + apply (CRlt_le_trans _ _ _ H).
      destruct (Radd_comm r1 (CRopp R r2)). exact H0.
Qed.

Lemma CRopp_lt_cancel : forall {R : ConstructiveReals} (r1 r2 : CRcarrier R),
    - r2 < - r1 -> r1 < r2.
Proof.
  intros. apply (CRplus_lt_compat_r r1) in H.
  rewrite (CRplus_opp_l r1) in H.
  apply (CRplus_lt_compat_l R r2) in H.
  rewrite CRplus_0_r, (Radd_assoc (CRisRing R)) in H.
  rewrite CRplus_opp_r, (Radd_0_l (CRisRing R)) in H.
  exact H.
Qed.

Lemma CRopp_ge_le_contravar
  : forall {R : ConstructiveReals} (r1 r2 : CRcarrier R),
    r2 <= r1 -> - r1 <= - r2.
Proof.
  intros. intros abs. apply CRopp_lt_cancel in abs. contradiction.
Qed.

Lemma CRopp_plus_distr : forall {R : ConstructiveReals} (r1 r2 : CRcarrier R),
    - (r1 + r2) == - r1 + - r2.
Proof.
  intros. destruct (CRisRing R), (CRisRingExt R).
  apply (CRplus_eq_reg_l (CRplus R r1 r2)).
  transitivity (CR_of_Q R 0). 1:apply Ropp_def.
  transitivity (r2 + r1 + (-r1 + -r2)).
  1:transitivity (r2 + (r1 + (-r1 + -r2))).
  1:transitivity (r2 + - r2).
  - apply CReq_sym. apply Ropp_def.
  - apply Radd_ext.
    + apply CReq_refl.
    + transitivity (0 + - r2).
      * apply CReq_sym, Radd_0_l.
      * transitivity (r1 + - r1 + - r2).
        -- apply Radd_ext. 2: apply CReq_refl. apply CReq_sym, Ropp_def.
        -- apply CReq_sym, Radd_assoc.
  - apply Radd_assoc.
  - apply Radd_ext. 2: apply CReq_refl. apply Radd_comm.
Qed.

Lemma CRmult_1_l : forall {R : ConstructiveReals} (r : CRcarrier R),
    1 * r == r.
Proof.
  intros. destruct (CRisRing R). apply Rmul_1_l.
Qed.

Lemma CRmult_1_r : forall {R : ConstructiveReals} (x : CRcarrier R),
    x * 1 == x.
Proof.
  intros. destruct (CRisRing R). transitivity (CRmult R 1 x).
  - apply Rmul_comm.
  - apply Rmul_1_l.
Qed.

Lemma CRmult_assoc : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    r * r1 * r2 == r * (r1 * r2).
Proof.
  intros. symmetry. apply (Rmul_assoc (CRisRing R)).
Qed.

Lemma CRmult_comm : forall {R : ConstructiveReals} (r s : CRcarrier R),
    r * s == s * r.
Proof.
  intros. rewrite (Rmul_comm (CRisRing R) r). reflexivity.
Qed.

Lemma CRmult_plus_distr_l : forall {R : ConstructiveReals} (r1 r2 r3 : CRcarrier R),
    r1 * (r2 + r3) == (r1 * r2) + (r1 * r3).
Proof.
  intros. destruct (CRisRing R).
  transitivity ((r2 + r3) * r1).
  - apply Rmul_comm.
  - transitivity ((r2 * r1) + (r3 * r1)).
    + apply Rdistr_l.
    + transitivity ((r1 * r2) + (r3 * r1)).
      * destruct (CRisRingExt R). apply Radd_ext.
        -- apply Rmul_comm.
        -- apply CReq_refl.
      * destruct (CRisRingExt R). apply Radd_ext.
        -- apply CReq_refl.
        -- apply Rmul_comm.
Qed.

Lemma CRmult_plus_distr_r : forall {R : ConstructiveReals} (r1 r2 r3 : CRcarrier R),
    (r2 + r3) * r1 == (r2 * r1) + (r3 * r1).
Proof.
  intros. do 3 rewrite <- (CRmult_comm r1).
  apply CRmult_plus_distr_l.
Qed.

(* x == x+x -> x == 0 *)
Lemma CRzero_double : forall {R : ConstructiveReals} (x : CRcarrier R),
    x == x + x -> x == 0.
Proof.
  intros.
  apply (CRplus_eq_reg_l x), CReq_sym. transitivity x.
  - apply CRplus_0_r.
  - exact H.
Qed.

Lemma CRmult_0_r : forall {R : ConstructiveReals} (x : CRcarrier R),
    x * 0 == 0.
Proof.
  intros. apply CRzero_double.
  transitivity (x * (0 + 0)).
  - destruct (CRisRingExt R). apply Rmul_ext.
    + apply CReq_refl.
    + apply CReq_sym, CRplus_0_r.
  - destruct (CRisRing R). apply CRmult_plus_distr_l.
Qed.

Lemma CRmult_0_l : forall {R : ConstructiveReals} (r : CRcarrier R),
    0 * r == 0.
Proof.
  intros. rewrite CRmult_comm. apply CRmult_0_r.
Qed.

Lemma CRopp_mult_distr_r : forall {R : ConstructiveReals} (r1 r2 : CRcarrier R),
    - (r1 * r2) == r1 * (- r2).
Proof.
  intros. apply (CRplus_eq_reg_l (CRmult R r1 r2)).
  destruct (CRisRing R). transitivity (CR_of_Q R 0). 1:apply Ropp_def.
  transitivity (r1 * (r2 + - r2)).
  2: apply CRmult_plus_distr_l.
  transitivity (r1 * 0).
  1:apply CReq_sym, CRmult_0_r.
  destruct (CRisRingExt R). apply Rmul_ext.
  - apply CReq_refl.
  - apply CReq_sym, Ropp_def.
Qed.

Lemma CRopp_mult_distr_l : forall {R : ConstructiveReals} (r1 r2 : CRcarrier R),
    - (r1 * r2) == (- r1) * r2.
Proof.
  intros. transitivity (r2 * - r1).
  1:transitivity (- (r2 * r1)).
  - apply (Ropp_ext (CRisRingExt R)).
    apply CReq_sym, (Rmul_comm (CRisRing R)).
  - apply CRopp_mult_distr_r.
  - apply CReq_sym, (Rmul_comm (CRisRing R)).
Qed.

Lemma CRmult_lt_compat_r : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    0 < r -> r1 < r2 -> r1 * r < r2 * r.
Proof.
  intros. apply (CRplus_lt_reg_r (CRopp R (CRmult R r1 r))).
  apply (CRle_lt_trans _ 0).
  1:apply (Ropp_def (CRisRing R)).
  apply (CRlt_le_trans _ (CRplus R (CRmult R r2 r) (CRmult R (CRopp R r1) r))).
  1:apply (CRlt_le_trans _ (CRmult R (CRplus R r2 (CRopp R r1)) r)).
  - apply CRmult_lt_0_compat. 2: exact H.
    apply (CRplus_lt_reg_r r1).
    apply (CRle_lt_trans _ r1).
    + apply (Radd_0_l (CRisRing R)).
    + apply (CRlt_le_trans _ r2 _ H0).
      apply (CRle_trans _ (CRplus R r2 (CRplus R (CRopp R r1) r1))).
      1:apply (CRle_trans _ (CRplus R r2 0)).
      * destruct (CRplus_0_r r2). exact H1.
      * apply CRplus_le_compat_l. destruct (CRplus_opp_l r1). exact H1.
      * destruct (Radd_assoc (CRisRing R) r2 (CRopp R r1) r1). exact H2.
  - destruct (CRisRing R).
    destruct (Rdistr_l r2 (CRopp R r1) r). exact H2.
  - apply CRplus_le_compat_l. destruct (CRopp_mult_distr_l r1 r).
    exact H1.
Qed.

Lemma CRmult_lt_compat_l : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    0 < r -> r1 < r2 -> r * r1 < r * r2.
Proof.
  intros. do 2 rewrite (CRmult_comm r).
  apply CRmult_lt_compat_r; assumption.
Qed.

Lemma CRinv_r : forall {R : ConstructiveReals} (r:CRcarrier R)
                  (rnz : r ≶ 0),
    r * (/ r) rnz == 1.
Proof.
  intros. transitivity ((/ r) rnz * r).
  - apply (CRisRing R).
  - apply CRinv_l.
Qed.

Lemma CRmult_lt_reg_r : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    0 < r -> r1 * r < r2 * r -> r1 < r2.
Proof.
  intros. apply (CRmult_lt_compat_r ((/ r) (inr H))) in H0.
  2: apply CRinv_0_lt_compat, H.
  apply (CRle_lt_trans _ ((r1 * r) * ((/ r) (inr H)))).
  - clear H0. apply (CRle_trans _ (CRmult R r1 1)).
    + destruct (CRmult_1_r r1). exact H0.
    + apply (CRle_trans _ (CRmult R r1 (CRmult R r ((/ r) (inr H))))).
      * destruct (Rmul_ext (CRisRingExt R) r1 r1 (CReq_refl r1)
                           (r * ((/ r) (inr H))) 1).
        -- apply CRinv_r.
        -- exact H0.
      * destruct (Rmul_assoc (CRisRing R) r1 r ((/ r) (inr H))). exact H1.
  - apply (CRlt_le_trans _ ((r2 * r) * ((/ r) (inr H)))).
    { exact H0. }
    clear H0.
    apply (CRle_trans _ (r2 * 1)).
    2: destruct (CRmult_1_r r2); exact H1.
    apply (CRle_trans _ (r2 * (r * ((/ r) (inr H))))).
    { destruct (Rmul_assoc (CRisRing R) r2 r ((/ r) (inr H))). exact H0. }
    destruct (Rmul_ext (CRisRingExt R) r2 r2 (CReq_refl r2)
                       (r * ((/ r) (inr H))) 1).
    + apply CRinv_r.
    + exact H1.
Qed.

Lemma CRmult_lt_reg_l : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    0 < r -> r * r1 < r * r2 -> r1 < r2.
Proof.
  intros.
  rewrite (Rmul_comm (CRisRing R) r r1) in H0.
  rewrite (Rmul_comm (CRisRing R) r r2) in H0.
  apply CRmult_lt_reg_r in H0.
  - exact H0.
  - exact H.
Qed.

Lemma CRmult_le_compat_l_half : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    0 < r -> r1 <= r2 -> r * r1 <= r * r2.
Proof.
  intros. intro abs. apply CRmult_lt_reg_l in abs.
  - contradiction.
  - exact H.
Qed.

Lemma CRmult_le_compat_r_half : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    0 < r
    -> r1 <= r2
    -> r1 * r <= r2 * r.
Proof.
  intros. intro abs. apply CRmult_lt_reg_r in abs.
  - contradiction.
  - exact H.
Qed.

Lemma CRmult_eq_reg_r : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    0 ≶ r
    -> r1 * r == r2 * r
    -> r1 == r2.
Proof.
  intros. destruct H0,H.
  - split.
    + intro abs. apply H0. apply CRmult_lt_compat_r.
      * exact c.
      * exact abs.
    + intro abs. apply H1. apply CRmult_lt_compat_r.
      * exact c.
      * exact abs.
  - split.
    + intro abs. apply H1. apply CRopp_lt_cancel.
      apply (CRle_lt_trans _ (CRmult R r1 (CRopp R r))).
      { apply CRopp_mult_distr_r. }
      apply (CRlt_le_trans _ (CRmult R r2 (CRopp R r))).
      2: apply CRopp_mult_distr_r.
      apply CRmult_lt_compat_r. 2: exact abs.
      apply (CRplus_lt_reg_r r). apply (CRle_lt_trans _ r).
      { apply (Radd_0_l (CRisRing R)). }
      apply (CRlt_le_trans _ 0 _ c).
      apply CRplus_opp_l.
    + intro abs. apply H0. apply CRopp_lt_cancel.
      apply (CRle_lt_trans _ (CRmult R r2 (CRopp R r))).
      1:apply CRopp_mult_distr_r.
      apply (CRlt_le_trans _ (CRmult R r1 (CRopp R r))).
      2: apply CRopp_mult_distr_r.
      apply CRmult_lt_compat_r. 2: exact abs.
      apply (CRplus_lt_reg_r r). apply (CRle_lt_trans _ r).
      1:apply (Radd_0_l (CRisRing R)).
      apply (CRlt_le_trans _ 0 _ c).
      apply CRplus_opp_l.
Qed.

Lemma CRinv_1 : forall {R : ConstructiveReals} (onz : CRapart R 1 0),
    (/ 1) onz == 1.
Proof.
  intros. rewrite <- (CRmult_1_r ((/ 1) onz)).
  rewrite CRinv_l. reflexivity.
Qed.

Lemma CRmult_eq_reg_l : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    r ≶ 0
    -> r * r1 == r * r2
    -> r1 == r2.
Proof.
  intros. rewrite (Rmul_comm (CRisRing R)) in H0.
  rewrite (Rmul_comm (CRisRing R) r) in H0.
  apply CRmult_eq_reg_r in H0.
  - exact H0.
  - destruct H.
    + right. exact c.
    + left. exact c.
Qed.

Lemma CRinv_mult_distr :
  forall {R : ConstructiveReals} (r1 r2 : CRcarrier R)
    (r1nz : r1 ≶ 0) (r2nz : r2 ≶ 0)
    (rmnz : (r1*r2) ≶ 0),
    (/ (r1 * r2)) rmnz == (/ r1) r1nz * (/ r2) r2nz.
Proof.
  intros. apply (CRmult_eq_reg_l r1).
  - exact r1nz.
  - rewrite (Rmul_assoc (CRisRing R)). rewrite CRinv_r. rewrite CRmult_1_l.
    apply (CRmult_eq_reg_l r2).
    + exact r2nz.
    + rewrite CRinv_r. rewrite (Rmul_assoc (CRisRing R)).
      rewrite (CRmult_comm r2 r1). rewrite CRinv_r. reflexivity.
Qed.

Lemma CRinv_morph : forall {R : ConstructiveReals} (x y : CRcarrier R)
                      (rxnz : x ≶ 0) (rynz : y ≶ 0),
    x == y
    -> (/ x) rxnz == (/ y) rynz.
Proof.
  intros. apply (CRmult_eq_reg_l x).
  - exact rxnz.
  - rewrite CRinv_r, H, CRinv_r. reflexivity.
Qed.

Lemma CRlt_minus : forall {R : ConstructiveReals} (x y : CRcarrier R),
    x < y -> 0 < y - x.
Proof.
  intros. rewrite <- (CRplus_opp_r x).
  apply CRplus_lt_compat_r. exact H.
Qed.

Lemma CR_of_Q_le : forall {R : ConstructiveReals} (r q : Q),
    Qle r q
    -> CR_of_Q R r <= CR_of_Q R q.
Proof.
  intros. intro abs. apply lt_CR_of_Q in abs.
  exact (Qlt_not_le _ _ abs H).
Qed.

Add Parametric Morphism {R : ConstructiveReals} : (CR_of_Q R)
    with signature Qeq ==> CReq R
      as CR_of_Q_morph.
Proof.
  split; apply CR_of_Q_le; rewrite H; apply Qle_refl.
Qed.

Lemma eq_inject_Q : forall {R : ConstructiveReals} (q r : Q),
    CR_of_Q R q == CR_of_Q R r -> Qeq q r.
Proof.
  intros. destruct H. destruct (Q_dec q r).
  - destruct s.
    + exfalso. apply (CR_of_Q_lt R q r) in q0. contradiction.
    + exfalso. apply (CR_of_Q_lt R r q) in q0. contradiction.
  - exact q0.
Qed.

#[global]
Instance CR_of_Q_morph_T
  : forall {R : ConstructiveReals}, CMorphisms.Proper
      (CMorphisms.respectful Qeq (CReq R)) (CR_of_Q R).
Proof.
  intros R x y H. apply CR_of_Q_morph; assumption.
Qed.

Lemma CR_of_Q_opp : forall {R : ConstructiveReals} (q : Q),
    CR_of_Q R (-q) == - CR_of_Q R q.
Proof.
  intros. apply (CRplus_eq_reg_l (CR_of_Q R q)).
  transitivity (CR_of_Q R 0).
  - transitivity (CR_of_Q R (q-q)).
    + apply CReq_sym, CR_of_Q_plus.
    + apply CR_of_Q_morph. ring.
  - apply CReq_sym. apply (CRisRing R).
Qed.

Lemma CR_of_Q_pos : forall {R : ConstructiveReals} (q:Q),
    Qlt 0 q -> 0 < CR_of_Q R q.
Proof.
  intros. apply CR_of_Q_lt. exact H.
Qed.

Lemma CR_of_Q_inv : forall {R : ConstructiveReals} (q : Q) (qPos : Qlt 0 q),
    CR_of_Q R (/q)
    == (/ CR_of_Q R q) (inr (CR_of_Q_pos q qPos)).
Proof.
  intros.
  apply (CRmult_eq_reg_l (CR_of_Q R q)).
  - right. apply CR_of_Q_pos, qPos.
  - rewrite CRinv_r, <- CR_of_Q_mult.
    apply CR_of_Q_morph. field. intro abs.
    rewrite abs in qPos. exact (Qlt_irrefl 0 qPos).
Qed.

Lemma CRmult_le_0_compat : forall {R : ConstructiveReals} (a b : CRcarrier R),
    0 <= a -> 0 <= b -> 0 <= a * b.
Proof.
  (* Limit of (a + 1/n)*b when n -> infty. *)
  intros. intro abs.
  assert (0 < -(a*b)) as epsPos.
  { rewrite <- CRopp_0. apply CRopp_gt_lt_contravar. exact abs. }
  destruct (CR_archimedean R (b * ((/ -(a*b)) (inr epsPos))))
    as [n maj].
  assert (0 < CR_of_Q R (Z.pos n #1)) as nPos.
  { apply CR_of_Q_lt. reflexivity. }
  assert (b * (/ CR_of_Q R (Z.pos n #1)) (inr nPos) < -(a*b)).
  { apply (CRmult_lt_reg_r (CR_of_Q R (Z.pos n #1))).
    - apply nPos.
    - rewrite <- (Rmul_assoc (CRisRing R)), CRinv_l, CRmult_1_r.
      apply (CRmult_lt_compat_r (-(a*b))) in maj.
      + rewrite CRmult_assoc, CRinv_l, CRmult_1_r in maj.
        rewrite CRmult_comm. apply maj.
      + apply epsPos. }
  pose proof (CRmult_le_compat_l_half
                (a + (/ CR_of_Q R (Z.pos n #1)) (inr nPos)) 0 b).
  assert (0 + 0 < a + (/ CR_of_Q R (Z.pos n #1)) (inr nPos)).
  { apply CRplus_le_lt_compat.
    - apply H.
    - apply CRinv_0_lt_compat. apply nPos. }
  rewrite CRplus_0_l in H3. specialize (H2 H3 H0).
  clear H3. rewrite CRmult_0_r in H2.
  apply H2. clear H2. rewrite (Rdistr_l (CRisRing R)).
  apply (CRplus_lt_compat_l R (a*b)) in H1.
  rewrite CRplus_opp_r in H1.
  rewrite (CRmult_comm ((/ CR_of_Q R (Z.pos n # 1)) (inr nPos))).
  apply H1.
Qed.

Lemma CRmult_le_compat_l : forall {R : ConstructiveReals} (r r1 r2:CRcarrier R),
    0 <= r -> r1 <= r2 -> r * r1 <= r * r2.
Proof.
  intros. apply (CRplus_le_reg_r (-(r*r1))).
  rewrite CRplus_opp_r, CRopp_mult_distr_r.
  rewrite <- CRmult_plus_distr_l.
  apply CRmult_le_0_compat.
  - exact H.
  - apply (CRplus_le_reg_r r1).
    rewrite CRplus_0_l, CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    exact H0.
Qed.

Lemma CRmult_le_compat_r : forall {R : ConstructiveReals} (r r1 r2:CRcarrier R),
    0 <= r -> r1 <= r2 -> r1 * r <= r2 * r.
Proof.
  intros. do 2 rewrite <- (CRmult_comm r).
  apply CRmult_le_compat_l; assumption.
Qed.

Lemma CRmult_pos_pos
  : forall {R : ConstructiveReals} (x y : CRcarrier R),
    0 < x * y -> 0 <= x
    -> 0 <= y -> 0 < x.
Proof.
  intros. destruct (CRltLinear R). clear p.
  specialize (s 0 x 1 (CRzero_lt_one R)) as [H2|H2].
  - exact H2.
  - apply CRlt_asym in H2.
    apply (CRmult_le_compat_r y) in H2.
    2: exact H1. rewrite CRmult_1_l in H2.
    apply (CRlt_le_trans _ _ _ H) in H2.
    rewrite <- (CRmult_0_l y) in H.
    apply CRmult_lt_reg_r in H.
    + exact H.
    + exact H2.
Qed.

(* In particular x * y == 1 implies that 0 # x, 0 # y and
   that x and y are inverses of each other. *)
Lemma CRmult_pos_appart_zero
  : forall {R : ConstructiveReals} (x y : CRcarrier R),
    0 < x * y -> 0 ≶ x.
Proof.
  intros.
  (* Narrow cases to x < 1. *)
  destruct (CRltLinear R). clear p.
  pose proof (s 0 x 1 (CRzero_lt_one R)) as [H0|H0].
  { left. exact H0. }
  (* In this case, linear order 0 y (x*y) decides. *)
  destruct (s 0 y (x*y) H).
  - left. rewrite <- (CRmult_0_l y) in H. apply CRmult_lt_reg_r in H.
    + exact H.
    + exact c.
  - right. apply CRopp_lt_cancel. rewrite CRopp_0.
    apply (CRmult_pos_pos (-x) (-y)).
    + rewrite <- CRopp_mult_distr_l, CRopp_mult_distr_r, CRopp_involutive. exact H.
    + rewrite <- CRopp_0. apply CRopp_ge_le_contravar.
      intro abs. rewrite <- (CRmult_0_r x) in H.
      apply CRmult_lt_reg_l in H.
      * rewrite <- (CRmult_1_l y) in c.
        rewrite <- CRmult_assoc in c. apply CRmult_lt_reg_r in c.
        -- rewrite CRmult_1_r in c. exact (CRlt_asym _ _ H0 c).
        -- exact H.
      * exact abs.
    + intro abs. apply (CRmult_lt_compat_r y) in H0.
      * rewrite CRmult_1_l in H0. exact (CRlt_asym _ _ H0 c).
      * apply CRopp_lt_cancel. rewrite CRopp_0. exact abs.
Qed.

Lemma CRmult_le_reg_l :
  forall {R : ConstructiveReals} (x y z : CRcarrier R),
    0 < x -> x * y <= x * z -> y <= z.
Proof.
  intros. intro abs.
  apply (CRmult_lt_compat_l x) in abs.
  - contradiction.
  - exact H.
Qed.

Lemma CRmult_le_reg_r :
  forall {R : ConstructiveReals} (x y z : CRcarrier R),
    0 < x -> y * x <= z * x -> y <= z.
Proof.
  intros. intro abs.
  apply (CRmult_lt_compat_r x) in abs.
  - contradiction.
  - exact H.
Qed.

Definition CRup_nat {R : ConstructiveReals} (x : CRcarrier R)
  : { n : nat  &  x < CR_of_Q R (Z.of_nat n #1) }.
Proof.
  destruct (CR_archimedean R x). exists (Pos.to_nat x0).
  rewrite Znat.positive_nat_Z. exact c.
Qed.

Definition CRfloor {R : ConstructiveReals} (a : CRcarrier R)
  : { p : Z  &  prod (CR_of_Q R (p#1) < a)
                     (a < CR_of_Q R (p#1) + CR_of_Q R 2) }.
Proof.
  destruct (CR_Q_dense R (a - CR_of_Q R (1#2)) a) as [q qmaj].
  - apply (CRlt_le_trans _ (a-0)).
    + apply CRplus_lt_compat_l.
      apply CRopp_gt_lt_contravar.
      apply CR_of_Q_lt. reflexivity.
    + unfold CRminus. rewrite CRopp_0, CRplus_0_r. apply CRle_refl.
  - exists (Qfloor q). destruct qmaj. split.
    + apply (CRle_lt_trans _ (CR_of_Q R q)). 2: exact c0.
      apply CR_of_Q_le. apply Qfloor_le.
    + apply (CRlt_le_trans _ (CR_of_Q R q + CR_of_Q R (1#2))).
      * apply (CRplus_lt_compat_r (CR_of_Q R (1 # 2))) in c.
        unfold CRminus in c. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r in c. exact c.
      * rewrite (CR_of_Q_plus R 1 1), <- CRplus_assoc, <- (CR_of_Q_plus R _ 1).
        apply CRplus_le_compat.
        -- apply CR_of_Q_le.
           rewrite Qinv_plus_distr. apply Qlt_le_weak, Qlt_floor.
        -- apply CR_of_Q_le. discriminate.
Qed.

Lemma CRplus_appart_reg_l : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    (r + r1) ≶ (r + r2) -> r1 ≶ r2.
Proof.
  intros. destruct H.
  - left. apply (CRplus_lt_reg_l R r), c.
  - right. apply (CRplus_lt_reg_l R r), c.
Qed.

Lemma CRplus_appart_reg_r : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    (r1 + r) ≶ (r2 + r) -> r1 ≶ r2.
Proof.
  intros. destruct H.
  - left. apply (CRplus_lt_reg_r r), c.
  - right. apply (CRplus_lt_reg_r r), c.
Qed.

Lemma CRmult_appart_reg_l
  : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    0 < r -> (r * r1) ≶ (r * r2) -> r1 ≶ r2.
Proof.
  intros. destruct H0.
  - left. exact (CRmult_lt_reg_l r _ _ H c).
  - right. exact (CRmult_lt_reg_l r _ _ H c).
Qed.

Lemma CRmult_appart_reg_r
  : forall {R : ConstructiveReals} (r r1 r2 : CRcarrier R),
    0 < r -> (r1 * r) ≶ (r2 * r) -> r1 ≶ r2.
Proof.
  intros. destruct H0.
  - left. exact (CRmult_lt_reg_r r _ _ H c).
  - right. exact (CRmult_lt_reg_r r _ _ H c).
Qed.

#[global]
Instance CRapart_morph
  : forall {R : ConstructiveReals}, CMorphisms.Proper
      (CMorphisms.respectful (CReq R) (CMorphisms.respectful (CReq R) CRelationClasses.iffT)) (CRapart R).
Proof.
  intros R x y H x0 y0 H0. destruct H, H0. split.
  - intro. destruct H3.
    + left. apply (CRle_lt_trans _ x _ H).
      apply (CRlt_le_trans _ x0 _ c), H2.
    + right. apply (CRle_lt_trans _ x0 _ H0).
      apply (CRlt_le_trans _ x _ c), H1.
  - intro. destruct H3.
    + left. apply (CRle_lt_trans _ y _ H1).
      apply (CRlt_le_trans _ y0 _ c), H0.
    + right. apply (CRle_lt_trans _ y0 _ H2).
      apply (CRlt_le_trans _ y _ c), H.
Qed.
