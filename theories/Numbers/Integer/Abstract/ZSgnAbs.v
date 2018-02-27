(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Properties of [abs] and [sgn] *)

Require Import ZMulOrder.

(** Since we already have [max], we could have defined [abs]. *)

Module GenericAbs (Import Z : ZAxiomsMiniSig')
                  (Import ZP : ZMulOrderProp Z) <: HasAbs Z.
 Definition abs n := max n (-n).
 Lemma abs_eq : forall n, 0<=n -> abs n == n.
 Proof.
  intros. unfold abs. apply max_l.
  apply le_trans with 0; auto.
  rewrite opp_nonpos_nonneg; auto.
 Qed.
 Lemma abs_neq : forall n, n<=0 -> abs n == -n.
 Proof.
  intros. unfold abs. apply max_r.
  apply le_trans with 0; auto.
  rewrite opp_nonneg_nonpos; auto.
 Qed.
End GenericAbs.

(** We can deduce a [sgn] function from a [compare] function *)

Module Type ZDecAxiomsSig := ZAxiomsMiniSig <+ HasCompare.
Module Type ZDecAxiomsSig' := ZAxiomsMiniSig' <+ HasCompare.

Module Type GenericSgn (Import Z : ZDecAxiomsSig')
                       (Import ZP : ZMulOrderProp Z) <: HasSgn Z.
 Definition sgn n :=
  match compare 0 n with Eq => 0 | Lt => 1 | Gt => -1 end.
 Lemma sgn_null : forall n, n==0 -> sgn n == 0.
 Proof. unfold sgn; intros. destruct (compare_spec 0 n); order. Qed.
 Lemma sgn_pos : forall n, 0<n -> sgn n == 1.
 Proof. unfold sgn; intros. destruct (compare_spec 0 n); order. Qed.
 Lemma sgn_neg : forall n, n<0 -> sgn n == -1.
 Proof. unfold sgn; intros. destruct (compare_spec 0 n); order. Qed.
End GenericSgn.


(** Derived properties of [abs] and [sgn] *)

Module Type ZSgnAbsProp (Import Z : ZAxiomsSig')
                        (Import ZP : ZMulOrderProp Z).

Ltac destruct_max n :=
 destruct (le_ge_cases 0 n);
  [rewrite (abs_eq n) by auto | rewrite (abs_neq n) by auto].

Instance abs_wd : Proper (eq==>eq) abs.
Proof.
 intros x y EQ. destruct_max x.
 rewrite abs_eq; trivial. now rewrite <- EQ.
 rewrite abs_neq; try order. now rewrite opp_inj_wd.
Qed.

Lemma abs_max : forall n, abs n == max n (-n).
Proof.
 intros n. destruct_max n.
 rewrite max_l; auto with relations.
 apply le_trans with 0; auto.
 rewrite opp_nonpos_nonneg; auto.
 rewrite max_r; auto with relations.
 apply le_trans with 0; auto.
 rewrite opp_nonneg_nonpos; auto.
Qed.

Lemma abs_neq' : forall n, 0<=-n -> abs n == -n.
Proof.
 intros. apply abs_neq. now rewrite <- opp_nonneg_nonpos.
Qed.

Lemma abs_nonneg : forall n, 0 <= abs n.
Proof.
 intros n. destruct_max n; auto.
 now rewrite opp_nonneg_nonpos.
Qed.

Lemma abs_eq_iff : forall n, abs n == n <-> 0<=n.
Proof.
 split; try apply abs_eq. intros EQ.
 rewrite <- EQ. apply abs_nonneg.
Qed.

Lemma abs_neq_iff : forall n, abs n == -n <-> n<=0.
Proof.
 split; try apply abs_neq. intros EQ.
 rewrite <- opp_nonneg_nonpos, <- EQ. apply abs_nonneg.
Qed.

Lemma abs_opp : forall n, abs (-n) == abs n.
Proof.
 intros. destruct_max n.
 rewrite (abs_neq (-n)), opp_involutive. reflexivity.
 now rewrite opp_nonpos_nonneg.
 rewrite (abs_eq (-n)). reflexivity.
 now rewrite opp_nonneg_nonpos.
Qed.

Lemma abs_0 : abs 0 == 0.
Proof.
 apply abs_eq. apply le_refl.
Qed.

Lemma abs_0_iff : forall n, abs n == 0 <-> n==0.
Proof.
 split. destruct_max n; auto.
 now rewrite eq_opp_l, opp_0.
 intros EQ; rewrite EQ. rewrite abs_eq; auto using eq_refl, le_refl.
Qed.

Lemma abs_pos : forall n, 0 < abs n <-> n~=0.
Proof.
 intros. rewrite <- abs_0_iff. split; [intros LT| intros NEQ].
 intro EQ. rewrite EQ in LT. now elim (lt_irrefl 0).
 assert (LE : 0 <= abs n) by apply abs_nonneg.
 rewrite lt_eq_cases in LE; destruct LE; auto.
 elim NEQ; auto with relations.
Qed.

Lemma abs_eq_or_opp : forall n, abs n == n \/ abs n == -n.
Proof.
 intros. destruct_max n; auto with relations.
Qed.

Lemma abs_or_opp_abs : forall n, n == abs n \/ n == - abs n.
Proof.
 intros. destruct_max n; rewrite ? opp_involutive; auto with relations.
Qed.

Lemma abs_involutive : forall n, abs (abs n) == abs n.
Proof.
 intros. apply abs_eq. apply abs_nonneg.
Qed.

Lemma abs_spec : forall n,
  (0 <= n /\ abs n == n) \/ (n < 0 /\ abs n == -n).
Proof.
 intros. destruct (le_gt_cases 0 n).
 left; split; auto. now apply abs_eq.
 right; split; auto. apply abs_neq. now apply lt_le_incl.
Qed.

Lemma abs_case_strong :
  forall (P:t->Prop) n, Proper (eq==>iff) P ->
    (0<=n -> P n) -> (n<=0 -> P (-n)) -> P (abs n).
Proof.
 intros. destruct_max n; auto.
Qed.

Lemma abs_case : forall (P:t->Prop) n, Proper (eq==>iff) P ->
 P n -> P (-n) -> P (abs n).
Proof. intros. now apply abs_case_strong. Qed.

Lemma abs_eq_cases : forall n m, abs n == abs m -> n == m \/ n == - m.
Proof.
 intros n m EQ. destruct (abs_or_opp_abs n) as [EQn|EQn].
 rewrite EQn, EQ. apply abs_eq_or_opp.
 rewrite EQn, EQ, opp_inj_wd, eq_opp_l, or_comm. apply abs_eq_or_opp.
Qed.

Lemma abs_lt : forall a b, abs a < b <-> -b < a < b.
Proof.
 intros a b.
 destruct (abs_spec a) as [[LE EQ]|[LT EQ]]; rewrite EQ; clear EQ.
 split; try split; try destruct 1; try order.
 apply lt_le_trans with 0; trivial. apply opp_neg_pos; order.
 rewrite opp_lt_mono, opp_involutive.
 split; try split; try destruct 1; try order.
 apply lt_le_trans with 0; trivial. apply opp_nonpos_nonneg; order.
Qed.

Lemma abs_le : forall a b, abs a <= b <-> -b <= a <= b.
Proof.
 intros a b.
 destruct (abs_spec a) as [[LE EQ]|[LT EQ]]; rewrite EQ; clear EQ.
 split; try split; try destruct 1; try order.
 apply le_trans with 0; trivial. apply opp_nonpos_nonneg; order.
 rewrite opp_le_mono, opp_involutive.
 split; try split; try destruct 1; try order.
 apply le_trans with 0. order. apply opp_nonpos_nonneg; order.
Qed.

(** Triangular inequality *)

Lemma abs_triangle : forall n m, abs (n + m) <= abs n + abs m.
Proof.
 intros. destruct_max n; destruct_max m.
 rewrite abs_eq. apply le_refl. now apply add_nonneg_nonneg.
 destruct_max (n+m); try rewrite opp_add_distr;
  apply add_le_mono_l || apply add_le_mono_r.
 apply le_trans with 0; auto. now rewrite opp_nonneg_nonpos.
 apply le_trans with 0; auto. now rewrite opp_nonpos_nonneg.
 destruct_max (n+m); try rewrite opp_add_distr;
  apply add_le_mono_l || apply add_le_mono_r.
 apply le_trans with 0; auto. now rewrite opp_nonneg_nonpos.
 apply le_trans with 0; auto. now rewrite opp_nonpos_nonneg.
 rewrite abs_neq, opp_add_distr. apply le_refl.
 now apply add_nonpos_nonpos.
Qed.

Lemma abs_sub_triangle : forall n m, abs n - abs m <= abs (n-m).
Proof.
 intros.
 rewrite le_sub_le_add_l, add_comm.
 rewrite <- (sub_simpl_r n m) at 1.
 apply abs_triangle.
Qed.

(** Absolute value and multiplication *)

Lemma abs_mul : forall n m, abs (n * m) == abs n * abs m.
Proof.
 assert (H : forall n m, 0<=n -> abs (n*m) == n * abs m).
  intros. destruct_max m.
  rewrite abs_eq. apply eq_refl. now apply mul_nonneg_nonneg.
  rewrite abs_neq, mul_opp_r. reflexivity. now apply mul_nonneg_nonpos .
 intros. destruct_max n. now apply H.
 rewrite <- mul_opp_opp, H, abs_opp. reflexivity.
 now apply opp_nonneg_nonpos.
Qed.

Lemma abs_square : forall n, abs n * abs n == n * n.
Proof.
 intros. rewrite <- abs_mul. apply abs_eq. apply le_0_square.
Qed.

(** Some results about the sign function. *)

Ltac destruct_sgn n :=
 let LT := fresh "LT" in
 let EQ := fresh "EQ" in
 let GT := fresh "GT" in
 destruct (lt_trichotomy 0 n) as [LT|[EQ|GT]];
 [rewrite (sgn_pos n) by auto|
  rewrite (sgn_null n) by auto with relations|
  rewrite (sgn_neg n) by auto].

Instance sgn_wd : Proper (eq==>eq) sgn.
Proof.
 intros x y Hxy. destruct_sgn x.
 rewrite sgn_pos; auto with relations. rewrite <- Hxy; auto.
 rewrite sgn_null; auto with relations. rewrite <- Hxy; auto with relations.
 rewrite sgn_neg; auto with relations. rewrite <- Hxy; auto.
Qed.

Lemma sgn_spec : forall n,
  0 < n /\ sgn n == 1 \/
  0 == n /\ sgn n == 0 \/
  0 > n /\ sgn n == -1.
Proof.
 intros n.
 destruct_sgn n; [left|right;left|right;right]; auto with relations.
Qed.

Lemma sgn_0 : sgn 0 == 0.
Proof.
 now apply sgn_null.
Qed.

Lemma sgn_pos_iff : forall n, sgn n == 1 <-> 0<n.
Proof.
 split; try apply sgn_pos. destruct_sgn n; auto.
 intros. elim (lt_neq 0 1); auto. apply lt_0_1.
 intros. elim (lt_neq (-1) 1); auto.
 apply lt_trans with 0. rewrite opp_neg_pos. apply lt_0_1. apply lt_0_1.
Qed.

Lemma sgn_null_iff : forall n, sgn n == 0 <-> n==0.
Proof.
 split; try apply sgn_null. destruct_sgn n; auto with relations.
 intros. elim (lt_neq 0 1); auto with relations. apply lt_0_1.
 intros. elim (lt_neq (-1) 0); auto.
 rewrite opp_neg_pos. apply lt_0_1.
Qed.

Lemma sgn_neg_iff : forall n, sgn n == -1 <-> n<0.
Proof.
 split; try apply sgn_neg. destruct_sgn n; auto with relations.
 intros. elim (lt_neq (-1) 1); auto with relations.
 apply lt_trans with 0. rewrite opp_neg_pos. apply lt_0_1. apply lt_0_1.
 intros. elim (lt_neq (-1) 0); auto with relations.
 rewrite opp_neg_pos. apply lt_0_1.
Qed.

Lemma sgn_opp : forall n, sgn (-n) == - sgn n.
Proof.
 intros. destruct_sgn n.
 apply sgn_neg. now rewrite opp_neg_pos.
 setoid_replace n with 0 by auto with relations.
  rewrite opp_0. apply sgn_0.
 rewrite opp_involutive. apply sgn_pos. now rewrite opp_pos_neg.
Qed.

Lemma sgn_nonneg : forall n, 0 <= sgn n <-> 0 <= n.
Proof.
 split.
 destruct_sgn n; intros.
 now apply lt_le_incl.
 order.
 elim (lt_irrefl 0). apply lt_le_trans with 1; auto using lt_0_1.
  now rewrite <- opp_nonneg_nonpos.
 rewrite lt_eq_cases; destruct 1.
 rewrite sgn_pos by auto. apply lt_le_incl, lt_0_1.
 rewrite sgn_null by auto with relations. apply le_refl.
Qed.

Lemma sgn_nonpos : forall n, sgn n <= 0 <-> n <= 0.
Proof.
 intros. rewrite <- 2 opp_nonneg_nonpos, <- sgn_opp. apply sgn_nonneg.
Qed.

Lemma sgn_mul : forall n m, sgn (n*m) == sgn n * sgn m.
Proof.
 intros. destruct_sgn n; nzsimpl.
 destruct_sgn m.
  apply sgn_pos. now apply mul_pos_pos.
  apply sgn_null. rewrite eq_mul_0; auto with relations.
  apply sgn_neg. now apply mul_pos_neg.
 apply sgn_null. rewrite eq_mul_0; auto with relations.
 destruct_sgn m; try rewrite mul_opp_opp; nzsimpl.
  apply sgn_neg. now apply mul_neg_pos.
  apply sgn_null. rewrite eq_mul_0; auto with relations.
  apply sgn_pos. now apply mul_neg_neg.
Qed.

Lemma sgn_abs : forall n, n * sgn n == abs n.
Proof.
 intros. symmetry.
 destruct_sgn n; try rewrite mul_opp_r; nzsimpl.
 apply abs_eq. now apply lt_le_incl.
 rewrite abs_0_iff; auto with relations.
 apply abs_neq. now apply lt_le_incl.
Qed.

Lemma abs_sgn : forall n, abs n * sgn n == n.
Proof.
 intros.
 destruct_sgn n; try rewrite mul_opp_r; nzsimpl; auto.
 apply abs_eq. now apply lt_le_incl.
 rewrite eq_opp_l. apply abs_neq. now apply lt_le_incl.
Qed.

Lemma sgn_sgn : forall x, sgn (sgn x) == sgn x.
Proof.
 intros.
 destruct (sgn_spec x) as [(LT,EQ)|[(EQ',EQ)|(LT,EQ)]]; rewrite EQ.
 apply sgn_pos, lt_0_1.
 now apply sgn_null.
 apply sgn_neg. rewrite opp_neg_pos. apply lt_0_1.
Qed.

End ZSgnAbsProp.


