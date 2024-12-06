(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(**
* Lemmas about orders for modules implementing [NZOrdSig']

This file defines the [NZOrderProp] functor type, meant to be [Include]d in
a module implementing the [NZOrdSig'] module type.

It contains lemmas and tactics about [le], [lt] and [eq].

The firt part contains important basic lemmas about [le] and [lt], for instance
- [succ_lt_mono], [succ_le_mono], [lt_succ_diag_r], [le_succ_diag_r], ...
- [le_refl], [le_antisymm], [lt_asymm], [le_trans], [lt_trans], ...
- decidability lemmas like [le_gt_cases], [eq_decidable], ...
It also adds the following tactics:
- [le_elim H] to reason by cases on an hypothesis [(H) : n <= m]
- the domain-agnostic [order] (see [Stdlib.Structures.OrdersTac]) and [order']
  which knows that [0 < 1 < 2]

The second part proves many induction principles involving the orders and
defines the tactic notation [nzord_induct].
*)
From Stdlib.Numbers.NatInt Require Import NZAxioms NZBase.
From Stdlib.Logic Require Import Decidable.
From Stdlib.Structures Require Import OrdersTac.

Module Type NZOrderProp
 (Import NZ : NZOrdSig')(Import NZBase : NZBaseProp NZ).

(** ** Basic facts about [le], [lt], [eq] and [succ] *)

(** *** Direct consequences of the specifications of [lt] and [le] *)
#[global]
Instance le_wd : Proper (eq==>eq==>iff) le.
Proof.
intros n n' Hn m m' Hm. now rewrite <- !lt_succ_r, Hn, Hm.
Qed.

Ltac le_elim H := rewrite lt_eq_cases in H; destruct H as [H | H].

Theorem lt_le_incl : forall n m, n < m -> n <= m.
Proof.
intros. apply lt_eq_cases. now left.
Qed.

Theorem le_refl : forall n, n <= n.
Proof.
intro. apply lt_eq_cases. now right.
Qed.

Theorem lt_succ_diag_r : forall n, n < S n.
Proof.
intro n. rewrite lt_succ_r. apply le_refl.
Qed.

Theorem le_succ_diag_r : forall n, n <= S n.
Proof.
intro; apply lt_le_incl; apply lt_succ_diag_r.
Qed.

Theorem neq_succ_diag_l : forall n, S n ~= n.
Proof.
intros n H. apply (lt_irrefl n). rewrite <- H at 2. apply lt_succ_diag_r.
Qed.

Theorem neq_succ_diag_r : forall n, n ~= S n.
Proof.
intro n; apply neq_sym, neq_succ_diag_l.
Qed.

Theorem nlt_succ_diag_l : forall n, ~ S n < n.
Proof.
intros n H. apply (lt_irrefl (S n)). rewrite lt_succ_r. now apply lt_le_incl.
Qed.

Theorem nle_succ_diag_l : forall n, ~ S n <= n.
Proof.
intros n H; le_elim H.
+ false_hyp H nlt_succ_diag_l. + false_hyp H neq_succ_diag_l.
Qed.

Theorem le_succ_l : forall n m, S n <= m <-> n < m.
Proof.
intros n m; nzinduct m n.
- split; intro H. + false_hyp H nle_succ_diag_l. + false_hyp H lt_irrefl.
- intro m.
  rewrite (lt_eq_cases (S n) (S m)), !lt_succ_r, (lt_eq_cases n m), succ_inj_wd.
  rewrite or_cancel_r.
  + reflexivity.
  + intros LE EQ; rewrite EQ in LE; false_hyp LE nle_succ_diag_l.
  + intros LT EQ; rewrite EQ in LT; false_hyp LT lt_irrefl.
Qed.

(** Trichotomy *)

Theorem le_gt_cases : forall n m, n <= m \/ n > m.
Proof.
intros n m; nzinduct n m.
- left; apply le_refl.
- intro n. rewrite lt_succ_r, le_succ_l, !lt_eq_cases. intuition auto with relations.
Qed.

Theorem lt_trichotomy : forall n m,  n < m \/ n == m \/ m < n.
Proof.
intros n m. generalize (le_gt_cases n m); rewrite lt_eq_cases; tauto.
Qed.

Notation lt_eq_gt_cases := lt_trichotomy (only parsing).

(** *** Asymmetry and transitivity. *)

Theorem lt_asymm : forall n m, n < m -> ~ m < n.
Proof.
intros n m; nzinduct n m.
- intros H; false_hyp H lt_irrefl.
- intro n; split; intros H H1 H2.
  + apply lt_succ_r in H2. le_elim H2.
    * apply H; auto. apply le_succ_l. now apply lt_le_incl.
    * rewrite H2 in H1. false_hyp H1 nlt_succ_diag_l.
  + apply le_succ_l in H1. le_elim H1.
    * apply H; auto. rewrite lt_succ_r. now apply lt_le_incl.
    * rewrite <- H1 in H2. false_hyp H2 nlt_succ_diag_l.
Qed.

Notation lt_ngt := lt_asymm (only parsing).

Theorem lt_trans : forall n m p, n < m -> m < p -> n < p.
Proof.
intros n m p; nzinduct p m.
- intros _ H; false_hyp H lt_irrefl.
- intro p. rewrite 2 lt_succ_r.
  split; intros H H1 H2.
  + apply lt_le_incl; le_elim H2; [now apply H | now rewrite H2 in H1].
  + assert (n <= p) as H3 by (auto using lt_le_incl).
    le_elim H3.
    * assumption.
    * rewrite <- H3 in H2.
      elim (lt_asymm n m); auto.
Qed.

Theorem le_trans : forall n m p, n <= m -> m <= p -> n <= p.
Proof.
intros n m p. rewrite 3 lt_eq_cases.
intros [LT|EQ] [LT'|EQ']; try rewrite EQ; try rewrite <- EQ';
 generalize (lt_trans n m p); auto with relations.
Qed.

(** *** Some type classes about order *)

#[global]
Instance lt_strorder : StrictOrder lt.
Proof. split. - exact lt_irrefl. - exact lt_trans. Qed.

#[global]
Instance le_preorder : PreOrder le.
Proof. split. - exact le_refl. - exact le_trans. Qed.

#[global]
Instance le_partialorder : PartialOrder _ le.
Proof.
intros x y. compute. split.
- intro EQ; now rewrite EQ.
- rewrite 2 lt_eq_cases. intuition auto with relations. elim (lt_irrefl x). now transitivity y.
Qed.

(** *** Making the generic [order] tactic *)

Definition lt_compat := lt_wd.
Definition lt_total := lt_trichotomy.
Definition le_lteq := lt_eq_cases.

Module Private_OrderTac.
Module IsTotal.
 Definition eq_equiv := eq_equiv.
 Definition lt_strorder := lt_strorder.
 Definition lt_compat := lt_compat.
 Definition lt_total := lt_total.
 Definition le_lteq := le_lteq.
End IsTotal.
Module Tac := !MakeOrderTac NZ IsTotal.
End Private_OrderTac.
Ltac order := Private_OrderTac.Tac.order.

(** *** Some direct consequences of [order] *)

Theorem lt_neq : forall n m, n < m -> n ~= m.
Proof. order. Qed.

Theorem le_neq : forall n m, n < m <-> n <= m /\ n ~= m.
Proof. intuition order. Qed.

Theorem eq_le_incl : forall n m, n == m -> n <= m.
Proof. order. Qed.

Lemma lt_stepl : forall x y z, x < y -> x == z -> z < y.
Proof. order. Qed.

Lemma lt_stepr : forall x y z, x < y -> y == z -> x < z.
Proof. order. Qed.

Lemma le_stepl : forall x y z, x <= y -> x == z -> z <= y.
Proof. order. Qed.

Lemma le_stepr : forall x y z, x <= y -> y == z -> x <= z.
Proof. order. Qed.

Declare Left  Step lt_stepl.
Declare Right Step lt_stepr.
Declare Left  Step le_stepl.
Declare Right Step le_stepr.

Theorem le_lt_trans : forall n m p, n <= m -> m < p -> n < p.
Proof. order. Qed.

Theorem lt_le_trans : forall n m p, n < m -> m <= p -> n < p.
Proof. order. Qed.

Theorem le_antisymm : forall n m, n <= m -> m <= n -> n == m.
Proof. order. Qed.

(** *** More properties of [<] and [<=] with respect to [S] and [0] *)

Theorem le_succ_r : forall n m, n <= S m <-> n <= m \/ n == S m.
Proof.
intros n m; rewrite lt_eq_cases. now rewrite lt_succ_r.
Qed.

Theorem lt_succ_l : forall n m, S n < m -> n < m.
Proof.
intros n m H; apply le_succ_l; order.
Qed.

Theorem le_le_succ_r : forall n m, n <= m -> n <= S m.
Proof.
intros n m LE. apply lt_succ_r in LE. order.
Qed.

Theorem lt_lt_succ_r : forall n m, n < m -> n < S m.
Proof.
intros. rewrite lt_succ_r. order.
Qed.

Theorem succ_lt_mono : forall n m, n < m <-> S n < S m.
Proof.
intros n m. rewrite <- le_succ_l. symmetry. apply lt_succ_r.
Qed.

Theorem succ_le_mono : forall n m, n <= m <-> S n <= S m.
Proof.
intros n m. now rewrite 2 lt_eq_cases, <- succ_lt_mono, succ_inj_wd.
Qed.

Theorem lt_0_1 : 0 < 1.
Proof.
rewrite one_succ. apply lt_succ_diag_r.
Qed.

Theorem le_0_1 : 0 <= 1.
Proof.
apply lt_le_incl, lt_0_1.
Qed.

Theorem lt_1_2 : 1 < 2.
Proof.
rewrite two_succ. apply lt_succ_diag_r.
Qed.

Theorem lt_0_2 : 0 < 2.
Proof.
  transitivity 1. - apply lt_0_1. - apply lt_1_2.
Qed.

Theorem le_0_2 : 0 <= 2.
Proof.
apply lt_le_incl, lt_0_2.
Qed.

(** The order tactic enriched with some knowledge of 0,1,2 *)

Ltac order' := generalize lt_0_1 lt_1_2; order.

Theorem lt_1_l : forall n m, 0 < n -> n < m -> 1 < m.
Proof.
intros n m H1 H2. rewrite <- le_succ_l, <- one_succ in H1. order.
Qed.

(** *** More Trichotomy, decidability and double negation elimination *)

(** The following theorem is cleary redundant, but helps not to
remember whether one has to say [le_gt_cases] or [lt_ge_cases]. *)

Theorem lt_ge_cases : forall n m, n < m \/ n >= m.
Proof.
intros n m; destruct (le_gt_cases m n); intuition order.
Qed.

Theorem le_ge_cases : forall n m, n <= m \/ n >= m.
Proof.
intros n m; destruct (le_gt_cases n m); intuition order.
Qed.

Theorem lt_gt_cases : forall n m, n ~= m <-> n < m \/ n > m.
Proof.
intros n m; destruct (lt_trichotomy n m); intuition order.
Qed.

(** Decidability of equality, even though true in each finite ring, does not
have a uniform proof. Otherwise, the proof for two fixed numbers would
reduce to a normal form that will say if the numbers are equal or not,
which cannot be true in all finite rings. Therefore, we prove decidability
in the presence of order. *)

Theorem eq_decidable : forall n m, decidable (n == m).
Proof.
intros n m; destruct (lt_trichotomy n m) as [ | [ | ]];
 (right; order) || (left; order).
Qed.

(** DNE stands for double-negation elimination. *)

Theorem eq_dne : forall n m, ~ ~ n == m <-> n == m.
Proof.
intros n m; split; intro H.
- destruct (eq_decidable n m) as [H1 | H1].
  + assumption. + false_hyp H1 H.
- intro H1; now apply H1.
Qed.

Theorem le_ngt : forall n m, n <= m <-> ~ n > m.
Proof. intuition order. Qed.

(** Redundant but useful *)

Theorem nlt_ge : forall n m, ~ n < m <-> n >= m.
Proof. intuition order. Qed.

Theorem lt_decidable : forall n m, decidable (n < m).
Proof.
intros n m; destruct (le_gt_cases m n); [right|left]; order.
Qed.

Theorem lt_dne : forall n m, ~ ~ n < m <-> n < m.
Proof.
intros n m; split; intro H.
- destruct (lt_decidable n m) as [H1 | H1]; [assumption | false_hyp H1 H].
- intro H1; false_hyp H H1.
Qed.

Theorem nle_gt : forall n m, ~ n <= m <-> n > m.
Proof. intuition order. Qed.

(** Redundant but useful *)

Theorem lt_nge : forall n m, n < m <-> ~ n >= m.
Proof. intuition order. Qed.

Theorem le_decidable : forall n m, decidable (n <= m).
Proof.
intros n m; destruct (le_gt_cases n m); [left|right]; order.
Qed.

Theorem le_dne : forall n m, ~ ~ n <= m <-> n <= m.
Proof.
intros n m; split; intro H.
- destruct (le_decidable n m) as [H1 | H1]; [assumption | false_hyp H1 H].
- intro H1; false_hyp H H1.
Qed.

Theorem nlt_succ_r : forall n m, ~ m < S n <-> n < m.
Proof.
intros n m; rewrite lt_succ_r. intuition order.
Qed.

(** The difference between integers and natural numbers is that for
every integer there is a predecessor, which is not true for natural
numbers. However, for both classes, every number that is bigger than
some other number has a predecessor. The proof of this fact by regular
induction does not go through, so we need to use strong
(course-of-value) induction. *)

Theorem lt_exists_pred :
  forall z n, z < n -> exists k, n == S k /\ z <= k.
Proof.
intros z n Hzn. assert (exists m, n <= m) as [m Hnm] by now exists n.
revert n Hzn Hnm. nzinduct m z.
- order.
- intro m; split; intros IH n H1 H2.
  + apply le_succ_r in H2. destruct H2 as [H2 | H2].
    * now apply IH. * exists m. now split; [| rewrite <- lt_succ_r; rewrite <- H2].
  + apply IH. * assumption. * now apply le_le_succ_r.
Qed.

Lemma lt_succ_pred : forall z n, z < n -> S (P n) == n.
Proof.
 intros z n H.
 destruct (lt_exists_pred _ _ H) as (n' & EQ & LE).
 rewrite EQ. now rewrite pred_succ.
Qed.

(** ** Order-based induction principles *)

Section WF.

Variable z : t.

Let Rlt (n m : t) := z <= n < m.
Let Rgt (n m : t) := m < n <= z.

Instance Rlt_wd : Proper (eq ==> eq ==> iff) Rlt.
Proof.
intros x1 x2 H1 x3 x4 H2; unfold Rlt. now rewrite H1, H2.
Qed.

Instance Rgt_wd : Proper (eq ==> eq ==> iff) Rgt.
Proof.
intros x1 x2 H1 x3 x4 H2; unfold Rgt; now rewrite H1, H2.
Qed.

Theorem lt_wf : well_founded Rlt.
Proof.
intros a. constructor. revert a.
refine (central_induction _ _ z _ _).
- solve_proper.
- intros y [??]. order.
- intros x. split.
  + intros IH y [? [? | ->]%lt_succ_r%lt_eq_cases].
    * now apply IH.
    * now constructor.
  + intros IH y [? ?%lt_lt_succ_r]. now apply IH.
Qed.

Theorem gt_wf : well_founded Rgt.
Proof.
intros a. constructor. revert a.
refine (central_induction _ _ z _ _).
- solve_proper.
- intros y [??]. order.
- intros x. split.
  + intros IH y [?%lt_succ_l ?]. now apply IH.
  + intros IH y [[? | <-]%le_succ_l%lt_eq_cases ?].
    * now apply IH.
    * now constructor.
Qed.

End WF.

(** Stronger variant of induction with assumptions [n >= 0] ([n < 0])
in the induction step *)

Section Induction.

Variable A : t -> Prop.
Hypothesis A_wd : Proper (eq==>iff) A.

Section Center.

Variable z : t. (* A z is the basis of induction *)

Section RightInduction.

Let A' (n : t) := forall m, z <= m -> m < n -> A m.
Let right_step :=   forall n, z <= n -> A n -> A (S n).
Let right_step' :=  forall n, z <= n -> A' n -> A n.
Let right_step'' := forall n, A' n <-> A' (S n).

Theorem strong_right_induction: right_step' -> forall n, z <= n -> A n.
Proof.
intros Hstep. refine (well_founded_induction (lt_wf z) _ _).
intros x IH Hzx. apply Hstep; [trivial|].
intros y ??. apply IH; [split|]; order.
Qed.

Theorem right_induction : A z -> right_step -> forall n, z <= n -> A n.
Proof.
intros Az RS; apply strong_right_induction.
intros n H1 H2.
le_elim H1.
- apply lt_exists_pred in H1. destruct H1 as [k [H3 H4]].
  rewrite H3. apply RS; trivial. apply H2; trivial.
  rewrite H3; apply lt_succ_diag_r.
- rewrite <- H1; apply Az.
Qed.

Theorem right_induction' :
  (forall n, n <= z -> A n) -> right_step -> forall n, A n.
Proof.
intros L R n.
destruct (lt_trichotomy n z) as [H | [H | H]].
- apply L; now apply lt_le_incl.
- apply L; now apply eq_le_incl.
- apply right_induction.
  + apply L; now apply eq_le_incl.
  + assumption.
  + now apply lt_le_incl.
Qed.

Theorem strong_right_induction' :
  (forall n, n <= z -> A n) -> right_step' -> forall n, A n.
Proof.
intros L R n.
destruct (lt_trichotomy n z) as [H | [H | H]].
- apply L; now apply lt_le_incl.
- apply L; now apply eq_le_incl.
- apply strong_right_induction.
  + assumption. + now apply lt_le_incl.
Qed.

End RightInduction.

Section LeftInduction.

Let A' (n : t) := forall m, m <= z -> n <= m -> A m.
Let left_step :=   forall n, n < z -> A (S n) -> A n.
Let left_step' :=  forall n, n <= z -> A' (S n) -> A n.
Let left_step'' := forall n, A' n <-> A' (S n).

Theorem strong_left_induction: left_step' -> forall n, n <= z -> A n.
Proof.
intros Hstep. refine (well_founded_induction (gt_wf z) _ _).
intros x IH Hzx. apply Hstep; [trivial|].
intros y ? ?%le_succ_l. apply IH; [split|]; order.
Qed.

Theorem left_induction : A z -> left_step -> forall n, n <= z -> A n.
Proof.
intros Az LS; apply strong_left_induction.
intros n H1 H2. le_elim H1.
- apply LS; trivial. apply H2; [now apply le_succ_l | now apply eq_le_incl].
- rewrite H1; apply Az.
Qed.

Theorem left_induction' :
  (forall n, z <= n -> A n) -> left_step -> forall n, A n.
Proof.
intros R L n.
destruct (lt_trichotomy n z) as [H | [H | H]].
- apply left_induction.
  + apply R. now apply eq_le_incl.
  + assumption.
  + now apply lt_le_incl.
- rewrite H; apply R; now apply eq_le_incl.
- apply R; now apply lt_le_incl.
Qed.

Theorem strong_left_induction' :
  (forall n, z <= n -> A n) -> left_step' -> forall n, A n.
Proof.
intros R L n.
destruct (lt_trichotomy n z) as [H | [H | H]].
- apply strong_left_induction.
  + trivial. + now apply lt_le_incl.
- rewrite H; apply R; now apply eq_le_incl.
- apply R; now apply lt_le_incl.
Qed.

End LeftInduction.

Theorem order_induction :
  A z ->
  (forall n, z <= n -> A n -> A (S n)) ->
  (forall n, n < z  -> A (S n) -> A n) ->
    forall n, A n.
Proof.
intros Az RS LS n.
destruct (lt_trichotomy n z) as [H | [H | H]].
- now apply left_induction; [| | apply lt_le_incl].
- now rewrite H.
- now apply right_induction; [| | apply lt_le_incl].
Qed.

Theorem order_induction' :
  A z ->
  (forall n, z <= n -> A n -> A (S n)) ->
  (forall n, n <= z -> A n -> A (P n)) ->
    forall n, A n.
Proof.
intros Az AS AP n; apply order_induction; try assumption.
intros m H1 H2. apply AP in H2; [|now apply le_succ_l].
now rewrite pred_succ in H2.
Qed.

End Center.

Theorem order_induction_0 :
  A 0 ->
  (forall n, 0 <= n -> A n -> A (S n)) ->
  (forall n, n < 0  -> A (S n) -> A n) ->
    forall n, A n.
Proof. exact (order_induction 0). Qed.

Theorem order_induction'_0 :
  A 0 ->
  (forall n, 0 <= n -> A n -> A (S n)) ->
  (forall n, n <= 0 -> A n -> A (P n)) ->
    forall n, A n.
Proof. exact (order_induction' 0). Qed.

(** Elimination principle for [<] *)

Theorem lt_ind : forall (n : t),
  A (S n) ->
  (forall m, n < m -> A m -> A (S m)) ->
   forall m, n < m -> A m.
Proof.
intros n H1 H2 m H3.
apply right_induction with (S n); [assumption | | now apply le_succ_l].
intros; apply H2; try assumption. now apply le_succ_l.
Qed.

(** Elimination principle for [<=] *)

Theorem le_ind : forall (n : t),
  A n ->
  (forall m, n <= m -> A m -> A (S m)) ->
   forall m, n <= m -> A m.
Proof.
intros n H1 H2 m H3.
now apply right_induction with n.
Qed.

End Induction.

Tactic Notation "nzord_induct" ident(n) :=
  induction_maker n ltac:(apply order_induction_0).

Tactic Notation "nzord_induct" ident(n) constr(z) :=
  induction_maker n ltac:(apply order_induction with z).

(** Induction principles with respect to a measure *)

Section MeasureInduction.

Variable X : Type.
Variable f : X -> t.

Theorem measure_right_induction : forall (A : X -> Type) (z : t),
  (forall x, z <= f x -> (forall y, z <= f y < f x -> A y) -> A x) ->
  forall x, z <= f x -> A x.
Proof.
  intros A z IH x Hx.
  enough (H : forall y, f y = f x -> A y) by now apply H.
  induction (lt_wf z (f x)) as [n _ IH'].
  intros y Hy. subst n. apply (IH y Hx).
  intros y' Hy'. now apply (IH' _ Hy').
Defined.

Lemma measure_left_induction : forall (A : X -> Type) (z : t),
  (forall x, f x <= z -> (forall y, f x < f y <= z -> A y) -> A x) ->
  forall x, f x <= z -> A x.
Proof.
  intros A z IH x Hx.
  enough (H : forall y, f y = f x -> A y) by now apply H.
  induction (gt_wf z (f x)) as [n _ IH'].
  intros y Hy. subst n. apply (IH y Hx).
  intros y' Hy'. now apply (IH' _ Hy').
Defined.

End MeasureInduction.

End NZOrderProp.

(* If we have moreover a [compare] function, we can build
    an [OrderedType] structure. *)

(* Temporary workaround for bug #2949: remove this problematic + unused functor
Module NZOrderedType (NZ : NZDecOrdSig')
 <: DecidableTypeFull <: OrderedTypeFull
 := NZ <+ NZBaseProp <+ NZOrderProp <+ Compare2EqBool <+ HasEqBool2Dec.
*)
