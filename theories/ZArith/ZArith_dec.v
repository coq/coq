(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Sumbool.

Require Import BinInt.
Require Import Zorder.
Require Import Zcompare.
Local Open Scope Z_scope.

(* begin hide *)
(* Trivial, to deprecate? *)
Lemma Dcompare_inf : forall r:comparison, {r = Eq} + {r = Lt} + {r = Gt}.
Proof.
  induction r; auto.
Defined.
(* end hide *)

Lemma Zcompare_rect (P:Type) (n m:Z) :
  ((n ?= m) = Eq -> P) -> ((n ?= m) = Lt -> P) -> ((n ?= m) = Gt -> P) -> P.
Proof.
  intros H1 H2 H3.
  destruct (n ?= m); auto.
Defined.

Lemma Zcompare_rec (P:Set) (n m:Z) :
  ((n ?= m) = Eq -> P) -> ((n ?= m) = Lt -> P) -> ((n ?= m) = Gt -> P) -> P.
Proof. apply Zcompare_rect. Defined.

Notation Z_eq_dec := Z.eq_dec (compat "8.7").

Section decidability.

  Variables x y : Z.

  (** * Decidability of order on binary integers *)

  Definition Z_lt_dec : {x < y} + {~ x < y}.
  Proof.
    unfold Z.lt; case Z.compare; (now left) || (now right).
  Defined.

  Definition Z_le_dec : {x <= y} + {~ x <= y}.
  Proof.
    unfold Z.le; case Z.compare; (now left) || (right; tauto).
  Defined.

  Definition Z_gt_dec : {x > y} + {~ x > y}.
  Proof.
    unfold Z.gt; case Z.compare; (now left) || (now right).
  Defined.

  Definition Z_ge_dec : {x >= y} + {~ x >= y}.
  Proof.
    unfold Z.ge; case Z.compare; (now left) || (right; tauto).
  Defined.

  Definition Z_lt_ge_dec : {x < y} + {x >= y}.
  Proof.
    exact Z_lt_dec.
  Defined.

  Lemma Z_lt_le_dec : {x < y} + {y <= x}.
  Proof.
    elim Z_lt_ge_dec.
    * now left.
    * right; now apply Z.ge_le.
  Defined.

  Definition Z_le_gt_dec : {x <= y} + {x > y}.
  Proof.
    elim Z_le_dec; auto with arith.
    intro. right. Z.swap_greater. now apply Z.nle_gt.
  Defined.

  Definition Z_gt_le_dec : {x > y} + {x <= y}.
  Proof.
    exact Z_gt_dec.
  Defined.

  Definition Z_ge_lt_dec : {x >= y} + {x < y}.
  Proof.
    elim Z_ge_dec; auto with arith.
    intro. right. Z.swap_greater. now apply Z.lt_nge.
  Defined.

  Definition Z_le_lt_eq_dec : x <= y -> {x < y} + {x = y}.
  Proof.
    intro H.
    apply Zcompare_rec with (n := x) (m := y).
    intro. right. elim (Z.compare_eq_iff x y); auto with arith.
    intro. left. elim (Z.compare_eq_iff x y); auto with arith.
    intro H1. absurd (x > y); auto with arith.
  Defined.

End decidability.

(** * Cotransitivity of order on binary integers *)

Lemma Zlt_cotrans : forall n m:Z, n < m -> forall p:Z, {n < p} + {p < m}.
Proof.
  intros x y H z.
  case (Z_lt_ge_dec x z).
  intro.
  left.
  assumption.
  intro.
  right.
  apply Z.le_lt_trans with (m := x).
  apply Z.ge_le.
  assumption.
  assumption.
Defined.

Lemma Zlt_cotrans_pos : forall n m:Z, 0 < n + m -> {0 < n} + {0 < m}.
Proof.
  intros x y H.
  case (Zlt_cotrans 0 (x + y) H x).
  - now left.
  - right.
    apply Z.add_lt_mono_l with (p := x).
    now rewrite Z.add_0_r.
Defined.

Lemma Zlt_cotrans_neg : forall n m:Z, n + m < 0 -> {n < 0} + {m < 0}.
Proof.
  intros x y H; case (Zlt_cotrans (x + y) 0 H x); intro Hxy;
    [ right; apply Z.add_lt_mono_l with (p := x); rewrite Z.add_0_r | left ];
    assumption.
Defined.

Lemma not_Zeq_inf : forall n m:Z, n <> m -> {n < m} + {m < n}.
Proof.
  intros x y H.
  case Z_lt_ge_dec with x y.
  intro.
  left.
  assumption.
  intro H0.
  generalize (Z.ge_le _ _ H0).
  intro.
  case (Z_le_lt_eq_dec _ _ H1).
  intro.
  right.
  assumption.
  intro.
  apply False_rec.
  apply H.
  symmetry .
  assumption.
Defined.

Lemma Z_dec : forall n m:Z, {n < m} + {n > m} + {n = m}.
Proof.
  intros x y.
  case (Z_lt_ge_dec x y).
  intro H.
  left.
  left.
  assumption.
  intro H.
  generalize (Z.ge_le _ _ H).
  intro H0.
  case (Z_le_lt_eq_dec y x H0).
  intro H1.
  left.
  right.
  apply Z.lt_gt.
  assumption.
  intro.
  right.
  symmetry .
  assumption.
Defined.


Lemma Z_dec' : forall n m:Z, {n < m} + {m < n} + {n = m}.
Proof.
  intros x y.
  case (Z.eq_dec x y); intro H;
    [ right; assumption | left; apply (not_Zeq_inf _ _ H) ].
Defined.

(* begin hide *)
(* To deprecate ? *)
Corollary Z_zerop : forall x:Z, {x = 0} + {x <> 0}.
Proof.
  exact (fun x:Z => Z.eq_dec x 0).
Defined.

Corollary Z_notzerop : forall (x:Z), {x <> 0} + {x = 0}.
Proof (fun x => sumbool_not _ _ (Z_zerop x)).

Corollary Z_noteq_dec : forall (x y:Z), {x <> y} + {x = y}.
Proof (fun x y => sumbool_not _ _ (Z.eq_dec x y)).
(* end hide *)
