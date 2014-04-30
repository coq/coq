(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Field.
Require Import QArith.
Require Import Znumtheory.
Require Import Eqdep_dec.

(** [Qc] : A canonical representation of rational numbers.
   based on the setoid representation [Q]. *)

Record Qc : Set := Qcmake { this :> Q ; canon : Qred this = this }.

Delimit Scope Qc_scope with Qc.
Bind Scope Qc_scope with Qc.
Arguments Qcmake this%Q _.
Open Scope Qc_scope.

Lemma Qred_identity :
  forall q:Q, Z.gcd (Qnum q) (QDen q) = 1%Z -> Qred q = q.
Proof.
  unfold Qred; intros (a,b); simpl.
  generalize (Z.ggcd_gcd a ('b)) (Z.ggcd_correct_divisors a ('b)).
  intros.
  rewrite H1 in H; clear H1.
  destruct (Z.ggcd a ('b)) as (g,(aa,bb)); simpl in *; subst.
  destruct H0.
  rewrite Z.mul_1_l in H, H0.
  subst; simpl; auto.
Qed.

Lemma Qred_identity2 :
  forall q:Q, Qred q = q -> Z.gcd (Qnum q) (QDen q) = 1%Z.
Proof.
  unfold Qred; intros (a,b); simpl.
  generalize (Z.ggcd_gcd a ('b)) (Z.ggcd_correct_divisors a ('b)) (Z.gcd_nonneg a ('b)).
  intros.
  rewrite <- H; rewrite <- H in H1; clear H.
  destruct (Z.ggcd a ('b)) as (g,(aa,bb)); simpl in *; subst.
  injection H2; intros; clear H2.
  destruct H0.
  clear H0 H3.
  destruct g as [|g|g]; destruct bb as [|bb|bb]; simpl in *; try discriminate.
  f_equal.
  apply Pos.mul_reg_r with bb.
  injection H2; intros.
  rewrite <- H0.
  rewrite H; simpl; auto.
  elim H1; auto.
Qed.

Lemma Qred_iff : forall q:Q, Qred q = q <-> Z.gcd (Qnum q) (QDen q) = 1%Z.
Proof.
  split; intros.
  apply Qred_identity2; auto.
  apply Qred_identity; auto.
Qed.


Lemma Qred_involutive : forall q:Q, Qred (Qred q) = Qred q.
Proof.
  intros; apply Qred_complete.
  apply Qred_correct.
Qed.

Definition Q2Qc (q:Q) : Qc := Qcmake (Qred q) (Qred_involutive q).
Arguments Q2Qc q%Q.
Notation " !! " := Q2Qc : Qc_scope.

Lemma Qc_is_canon : forall q q' : Qc, q == q' -> q = q'.
Proof.
  intros (q,proof_q) (q',proof_q').
  simpl.
  intros H.
  assert (H0:=Qred_complete _ _ H).
  assert (q = q') by congruence.
  subst q'.
  assert (proof_q = proof_q').
  apply eq_proofs_unicity; auto; intros.
  repeat decide equality.
  congruence.
Qed.
Hint Resolve Qc_is_canon.

Notation " 0 " := (!!0) : Qc_scope.
Notation " 1 " := (!!1) : Qc_scope.

Definition Qcle (x y : Qc) := (x <= y)%Q.
Definition Qclt (x y : Qc) := (x < y)%Q.
Notation Qcgt := (fun x y : Qc => Qlt y x).
Notation Qcge := (fun x y : Qc => Qle y x).
Infix "<" := Qclt : Qc_scope.
Infix "<=" := Qcle : Qc_scope.
Infix ">" := Qcgt : Qc_scope.
Infix ">=" := Qcge : Qc_scope.
Notation "x <= y <= z" := (x<=y/\y<=z) : Qc_scope.
Notation "x < y < z" := (x<y/\y<z) : Qc_scope.

Definition Qccompare (p q : Qc) := (Qcompare p q).
Notation "p ?= q" := (Qccompare p q) : Qc_scope.

Lemma Qceq_alt : forall p q, (p = q) <-> (p ?= q) = Eq.
Proof.
  unfold Qccompare.
  intros; rewrite <- Qeq_alt.
  split; auto.
  intro H; rewrite H; auto with qarith.
Qed.

Lemma Qclt_alt : forall p q, (p<q) <-> (p?=q = Lt).
Proof.
  intros; exact (Qlt_alt p q).
Qed.

Lemma Qcgt_alt : forall p q, (p>q) <-> (p?=q = Gt).
Proof.
  intros; exact (Qgt_alt p q).
Qed.

Lemma Qle_alt : forall p q, (p<=q) <-> (p?=q <> Gt).
Proof.
  intros; exact (Qle_alt p q).
Qed.

Lemma Qge_alt : forall p q, (p>=q) <-> (p?=q <> Lt).
Proof.
  intros; exact (Qge_alt p q).
Qed.

(** equality on [Qc] is decidable: *)

Theorem Qc_eq_dec : forall x y:Qc, {x=y} + {x<>y}.
Proof.
  intros.
  destruct (Qeq_dec x y) as [H|H]; auto.
  right; contradict H; subst; auto with qarith.
Defined.

(** The addition, multiplication and opposite are defined
   in the straightforward way: *)

Definition Qcplus (x y : Qc) := !!(x+y).
Infix "+" := Qcplus : Qc_scope.
Definition Qcmult (x y : Qc) := !!(x*y).
Infix "*" := Qcmult : Qc_scope.
Definition Qcopp (x : Qc) := !!(-x).
Notation "- x" := (Qcopp x) : Qc_scope.
Definition Qcminus (x y : Qc) := x+-y.
Infix "-" := Qcminus : Qc_scope.
Definition Qcinv (x : Qc) := !!(/x).
Notation "/ x" := (Qcinv x) : Qc_scope.
Definition Qcdiv (x y : Qc) := x*/y.
Infix "/" := Qcdiv : Qc_scope.

(** [0] and [1] are apart *)

Lemma Q_apart_0_1 : 1 <> 0.
Proof.
  unfold Q2Qc.
  intros H; discriminate H.
Qed.

Ltac qc := match goal with
 | q:Qc |- _ => destruct q; qc
 | _ => apply Qc_is_canon; simpl; repeat rewrite Qred_correct
end.

Opaque Qred.

(** Addition is associative: *)

Theorem Qcplus_assoc : forall x y z, x+(y+z)=(x+y)+z.
Proof.
  intros; qc; apply Qplus_assoc.
Qed.

(** [0] is a neutral element for addition: *)

Lemma Qcplus_0_l : forall x, 0+x = x.
Proof.
  intros; qc; apply Qplus_0_l.
Qed.

Lemma Qcplus_0_r : forall x, x+0 = x.
Proof.
  intros; qc; apply Qplus_0_r.
Qed.

(** Commutativity of addition: *)

Theorem Qcplus_comm : forall x y, x+y = y+x.
Proof.
  intros; qc; apply Qplus_comm.
Qed.

(** Properties of [Qopp] *)

Lemma Qcopp_involutive : forall q, - -q = q.
Proof.
  intros; qc; apply Qopp_involutive.
Qed.

Theorem Qcplus_opp_r : forall q, q+(-q) = 0.
Proof.
  intros; qc; apply Qplus_opp_r.
Qed.

(** Multiplication is associative: *)

Theorem Qcmult_assoc : forall n m p, n*(m*p)=(n*m)*p.
Proof.
  intros; qc; apply Qmult_assoc.
Qed.

(** [1] is a neutral element for multiplication: *)

Lemma Qcmult_1_l : forall n, 1*n = n.
Proof.
  intros; qc; apply Qmult_1_l.
Qed.

Theorem Qcmult_1_r : forall n, n*1=n.
Proof.
  intros; qc; apply Qmult_1_r.
Qed.

(** Commutativity of multiplication *)

Theorem Qcmult_comm : forall x y, x*y=y*x.
Proof.
  intros; qc; apply Qmult_comm.
Qed.

(** Distributivity *)

Theorem Qcmult_plus_distr_r : forall x y z, x*(y+z)=(x*y)+(x*z).
Proof.
  intros; qc; apply Qmult_plus_distr_r.
Qed.

Theorem Qcmult_plus_distr_l : forall x y z, (x+y)*z=(x*z)+(y*z).
Proof.
  intros; qc; apply Qmult_plus_distr_l.
Qed.

(** Integrality *)

Theorem Qcmult_integral : forall x y, x*y=0 -> x=0 \/ y=0.
Proof.
  intros.
  destruct (Qmult_integral x y); try qc; auto.
  injection H; clear H; intros _ H.
  rewrite <- (Qred_correct (x*y)).
  rewrite <- (Qred_correct 0).
  rewrite H; auto with qarith.
Qed.

Theorem Qcmult_integral_l : forall x y, ~ x = 0 -> x*y = 0 -> y = 0.
Proof.
  intros; destruct (Qcmult_integral _ _ H0); tauto.
Qed.

(** Inverse and division. *)

Theorem Qcmult_inv_r : forall x, x<>0 -> x*(/x) = 1.
Proof.
  intros; qc; apply Qmult_inv_r; auto.
Qed.

Theorem Qcmult_inv_l : forall x, x<>0 -> (/x)*x = 1.
Proof.
  intros.
  rewrite Qcmult_comm.
  apply Qcmult_inv_r; auto.
Qed.

Lemma Qcinv_mult_distr : forall p q, / (p * q) = /p * /q.
Proof.
  intros; qc; apply Qinv_mult_distr.
Qed.

Theorem Qcdiv_mult_l : forall x y, y<>0 -> (x*y)/y = x.
Proof.
  unfold Qcdiv.
  intros.
  rewrite <- Qcmult_assoc.
  rewrite Qcmult_inv_r; auto.
  apply Qcmult_1_r.
Qed.

Theorem Qcmult_div_r : forall x y, ~ y = 0 -> y*(x/y) = x.
Proof.
  unfold Qcdiv.
  intros.
  rewrite Qcmult_assoc.
  rewrite Qcmult_comm.
  rewrite Qcmult_assoc.
  rewrite Qcmult_inv_l; auto.
  apply Qcmult_1_l.
Qed.

(** Properties of order upon Q. *)

Lemma Qcle_refl : forall x, x<=x.
Proof.
  unfold Qcle; intros; simpl; apply Qle_refl.
Qed.

Lemma Qcle_antisym : forall x y, x<=y -> y<=x -> x=y.
Proof.
  unfold Qcle; intros; simpl in *.
  apply Qc_is_canon; apply Qle_antisym; auto.
Qed.

Lemma Qcle_trans : forall x y z, x<=y -> y<=z -> x<=z.
Proof.
  unfold Qcle; intros; eapply Qle_trans; eauto.
Qed.

Lemma Qclt_not_eq : forall x y, x<y -> x<>y.
Proof.
  unfold Qclt; intros; simpl in *.
  intro; destruct (Qlt_not_eq _ _ H).
  subst; auto with qarith.
Qed.

(** Large = strict or equal *)

Lemma Qclt_le_weak : forall x y, x<y -> x<=y.
Proof.
  unfold Qcle, Qclt; intros; apply Qlt_le_weak; auto.
Qed.

Lemma Qcle_lt_trans : forall x y z, x<=y -> y<z -> x<z.
Proof.
  unfold Qcle, Qclt; intros; eapply Qle_lt_trans; eauto.
Qed.

Lemma Qclt_le_trans : forall x y z, x<y -> y<=z -> x<z.
Proof.
  unfold Qcle, Qclt; intros; eapply Qlt_le_trans; eauto.
Qed.

Lemma Qclt_trans : forall x y z, x<y -> y<z -> x<z.
Proof.
  unfold Qclt; intros; eapply Qlt_trans; eauto.
Qed.

(** [x<y] iff [~(y<=x)] *)

Lemma Qcnot_lt_le : forall x y, ~ x<y -> y<=x.
Proof.
  unfold Qcle, Qclt; intros; apply Qnot_lt_le; auto.
Qed.

Lemma Qcnot_le_lt : forall x y, ~ x<=y -> y<x.
Proof.
  unfold Qcle, Qclt; intros; apply Qnot_le_lt; auto.
Qed.

Lemma Qclt_not_le : forall x y, x<y -> ~ y<=x.
Proof.
  unfold Qcle, Qclt; intros; apply Qlt_not_le; auto.
Qed.

Lemma Qcle_not_lt : forall x y, x<=y -> ~ y<x.
Proof.
  unfold Qcle, Qclt; intros; apply Qle_not_lt; auto.
Qed.

Lemma Qcle_lt_or_eq : forall x y, x<=y -> x<y \/ x==y.
Proof.
  unfold Qcle, Qclt; intros; apply Qle_lt_or_eq; auto.
Qed.

(** Some decidability results about orders. *)

Lemma Qc_dec : forall x y, {x<y} + {y<x} + {x=y}.
Proof.
  unfold Qclt, Qcle; intros.
  destruct (Q_dec x y) as [H|H].
  left; auto.
  right; apply Qc_is_canon; auto.
Defined.

Lemma Qclt_le_dec : forall x y, {x<y} + {y<=x}.
Proof.
  unfold Qclt, Qcle; intros; apply Qlt_le_dec; auto.
Defined.

(** Compatibility of operations with respect to order. *)

Lemma Qcopp_le_compat : forall p q, p<=q -> -q <= -p.
Proof.
  unfold Qcle, Qcopp; intros; simpl in *.
  repeat rewrite Qred_correct.
  apply Qopp_le_compat; auto.
Qed.

Lemma Qcle_minus_iff : forall p q, p <= q <-> 0 <= q+-p.
Proof.
  unfold Qcle, Qcminus; intros; simpl in *.
  repeat rewrite Qred_correct.
  apply Qle_minus_iff; auto.
Qed.

Lemma Qclt_minus_iff : forall p q, p < q <-> 0 < q+-p.
Proof.
  unfold Qclt, Qcplus, Qcopp; intros; simpl in *.
  repeat rewrite Qred_correct.
  apply Qlt_minus_iff; auto.
Qed.

Lemma Qcplus_le_compat :
  forall x y z t, x<=y -> z<=t -> x+z <= y+t.
Proof.
  unfold Qcplus, Qcle; intros; simpl in *.
  repeat rewrite Qred_correct.
  apply Qplus_le_compat; auto.
Qed.

Lemma Qcmult_le_compat_r : forall x y z, x <= y -> 0 <= z -> x*z <= y*z.
Proof.
  unfold Qcmult, Qcle; intros; simpl in *.
  repeat rewrite Qred_correct.
  apply Qmult_le_compat_r; auto.
Qed.

Lemma Qcmult_lt_0_le_reg_r : forall x y z, 0 <  z  -> x*z <= y*z -> x <= y.
Proof.
  unfold Qcmult, Qcle, Qclt; intros; simpl in *.
  rewrite !Qred_correct in * |-.
  eapply Qmult_lt_0_le_reg_r; eauto.
Qed.

Lemma Qcmult_lt_compat_r : forall x y z, 0 < z  -> x < y -> x*z < y*z.
Proof.
  unfold Qcmult, Qclt; intros; simpl in *.
  rewrite !Qred_correct in *.
  eapply Qmult_lt_compat_r; eauto.
Qed.

(** Rational to the n-th power *)

Fixpoint Qcpower (q:Qc)(n:nat) : Qc :=
  match n with
    | O => 1
    | S n => q * (Qcpower q n)
  end.

Notation " q ^ n " := (Qcpower q n) : Qc_scope.

Lemma Qcpower_1 : forall n, 1^n = 1.
Proof.
  induction n; simpl; auto with qarith.
  rewrite IHn; auto with qarith.
Qed.

Lemma Qcpower_0 : forall n, n<>O -> 0^n = 0.
Proof.
  destruct n; simpl.
  destruct 1; auto.
  intros.
  now apply Qc_is_canon.
Qed.

Lemma Qcpower_pos : forall p n, 0 <= p -> 0 <= p^n.
Proof.
  induction n; simpl; auto with qarith.
  easy.
  intros.
  apply Qcle_trans with (0*(p^n)).
  easy.
  apply Qcmult_le_compat_r; auto.
Qed.

(** And now everything is easier concerning tactics: *)

(** A ring tactic for rational numbers *)

Definition Qc_eq_bool (x y : Qc) :=
  if Qc_eq_dec x y then true else false.

Lemma Qc_eq_bool_correct : forall x y : Qc, Qc_eq_bool x y = true -> x=y.
Proof.
  intros x y; unfold Qc_eq_bool; case (Qc_eq_dec x y); simpl; auto.
  intros _ H; inversion H.
Qed.

Definition Qcrt : ring_theory 0 1 Qcplus Qcmult Qcminus Qcopp (eq(A:=Qc)).
Proof.
  constructor.
  exact Qcplus_0_l.
  exact Qcplus_comm.
  exact Qcplus_assoc.
  exact Qcmult_1_l.
  exact Qcmult_comm.
  exact Qcmult_assoc.
  exact Qcmult_plus_distr_l.
  reflexivity.
  exact Qcplus_opp_r.
Qed.

Definition Qcft :
  field_theory 0%Qc 1%Qc Qcplus Qcmult Qcminus Qcopp Qcdiv Qcinv (eq(A:=Qc)).
Proof.
  constructor.
  exact Qcrt.
  exact Q_apart_0_1.
  reflexivity.
  exact Qcmult_inv_l.
Qed.

Add Field Qcfield : Qcft.

(** A field tactic for rational numbers *)

Example test_field : (forall x y : Qc, y<>0 -> (x/y)*y = x)%Qc.
intros.
field.
auto.
Qed.


Theorem Qc_decomp: forall x y: Qc,
  (Qred x = x -> Qred y = y -> (x:Q) = y)-> x = y.
Proof.
  intros (q, Hq) (q', Hq'); simpl; intros H.
  assert (H1 := H Hq Hq').
  subst q'.
  assert (Hq = Hq').
  apply Eqdep_dec.eq_proofs_unicity; auto; intros.
  repeat decide equality.
  congruence.
Qed.
