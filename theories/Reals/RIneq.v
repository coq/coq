(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(************************************************************************)

(*********************************************************)
(** * Basic lemmas for the classical real numbers        *)
(*********************************************************)

(** This file provides several hundred basic lemmas about foundamental
    operations on R:
    - addition denoted by [Rplus] (notation: infix [+]),
      opposite denoted by [Ropp] (notation: unary prefix [-]) and
      subtraction denoted by [Rminus] (notation: infix [-]);
    - multiplication denoted by [Rmult] (notation: infix [*]),
      inverse denoted by [Rinv] (notation: prefix [/]),
      division denoted by [Rdiv] (notation: infix [/]) and
      square denoted by [Rsqr] (notation: suffix [²])
    - orders [<], [>], [<=] and [>=]
    - injective morphisms:
      - [INR : nat -> R]
      - [IPR : positive -> R]
      - [IZR : Z -> R]

    All those lemmas are proved using a set of 17 "primitive" lemmas in
    [Raxioms.v] (plus the convenient choice that the inverse of 0 is 0 in
    [Rdefinitions.v]). These "primitive" lemmas are:
    - [Rplus_comm], [Rplus_assoc], [Rplus_0_l], [Rplus_opp_l]
    - [Rmult_comm], [Rmult_assoc], [Rmult_1_l], [Rinv_l]
    - [Rmult_plus_distr_l], [R1_neq_R0]
    - [Rlt_trans], [Rlt_asym], [Rplus_lt_compat_l], [Rmult_lt_compat_l]
    - [total_order_T]
    - [completeness], [archimed]

    This makes this file independent of the actual construction of the real
    numbers, since these 17 axioms characterize, up to isomorphism, the ordered
    field of real numbers.
 *)

Require Import RelationClasses.
Require Export Raxioms.
Require Import Rpow_def.
Require Import ZArith.
Require Export ZArithRing.
Require Export RealField.

Local Open Scope Z_scope.
Local Open Scope R_scope.

(*********************************************************)
(** ** Relation between orders and equality              *)
(*********************************************************)

(** Reflexivity of the large orders *)

Lemma Rle_refl : forall r, r <= r.
Proof. now intros r; right. Qed.
#[global]
Hint Immediate Rle_refl: rorders.

#[export] Instance Rle_Reflexive : Reflexive Rle | 10 := Rle_refl.

Lemma Rge_refl : forall r, r >= r.
Proof. now intros r; right. Qed.
#[global]
Hint Immediate Rge_refl: rorders.

#[export] Instance Rge_Reflexive : Reflexive Rge | 10 := Rge_refl.

Lemma Req_le : forall r1 r2, r1 = r2 -> r1 <= r2.
Proof. now intros r1 r2 H; right. Qed.
#[global]
Hint Immediate Req_le: real.

Lemma Req_ge : forall r1 r2, r1 = r2 -> r1 >= r2.
Proof. now intros r1 r2 H; right. Qed.
#[global]
Hint Immediate Req_ge: real.

(** Irreflexivity of the strict orders *)

Lemma Rlt_irrefl : forall r, ~ r < r.
Proof. intros r H; now apply (Rlt_asym r r). Qed.
#[global]
Hint Resolve Rlt_irrefl: real.

#[export] Instance Rlt_Irreflexive : Irreflexive Rlt | 10 := Rlt_irrefl.

Lemma Rgt_irrefl : forall r, ~ r > r.
Proof. exact Rlt_irrefl. Qed.

#[export] Instance Rgt_Irreflexive : Irreflexive Rgt | 10 := Rgt_irrefl.

Lemma Rlt_not_eq : forall r1 r2, r1 < r2 -> r1 <> r2.
Proof. now intros r1 r2 H H0; apply (Rlt_irrefl r1); rewrite H0 at 2. Qed.

Lemma Rgt_not_eq : forall r1 r2, r1 > r2 -> r1 <> r2.
Proof. now intros r1 r2 H1 H2%eq_sym; apply (Rlt_not_eq r2 r1). Qed.

Lemma Rlt_dichotomy_converse : forall r1 r2, r1 < r2 \/ r1 > r2 -> r1 <> r2.
Proof.
  intros r1 r2 [Hlt | Hgt].
  - now apply Rlt_not_eq.
  - now apply Rgt_not_eq.
Qed.
#[global]
Hint Resolve Rlt_dichotomy_converse: real.

(** Reasoning by case on equality and order *)

(* We should use Rtotal_order in proofs and total_order_T in definitions. *)
Lemma Rtotal_order : forall r1 r2, r1 < r2 \/ r1 = r2 \/ r1 > r2.
Proof.
  intros r1 r2; destruct (total_order_T r1 r2) as [[Hlt | Heq] | Hgt].
  - now left.
  - now right; left.
  - now right; right.
Qed.

Lemma Req_dec : forall r1 r2:R, r1 = r2 \/ r1 <> r2.
Proof.
  intros r1 r2; destruct (Rtotal_order r1 r2) as [Hlt | [Heq | Hgt]].
  - now right; apply Rlt_not_eq.
  - now left.
  - now right; apply Rgt_not_eq.
Qed.
#[global]
Hint Resolve Req_dec: real.

Lemma Rdichotomy : forall r1 r2, r1 <> r2 -> r1 < r2 \/ r1 > r2.
Proof.
  intros r1 r2 r1_neq_r2; destruct (Rtotal_order r1 r2) as [Hlt | [Heq | Hgt]].
  - now left.
  - now exfalso.
  - now right.
Qed.

(*********************************************************)
(** ** Strong decidable equality                          *)
(*********************************************************)

Lemma Req_dec_T : forall r1 r2:R, {r1 = r2} + {r1 <> r2}.
Proof.
  intros r1 r2; destruct (total_order_T r1 r2) as [[H | ] | H].
  - now right; intros ->; apply (Rlt_irrefl r2).
  - now left.
  - now right; intros ->; apply (Rlt_irrefl r2 H).
Qed.

(*********************************************************)
(** ** Relating [<], [>], [<=] and [>=]                  *)
(*********************************************************)

(** *** Relating strict and large orders *)

Lemma Rlt_le : forall r1 r2, r1 < r2 -> r1 <= r2.
Proof. now intros r1 r2 H; left. Qed.
#[global]
Hint Resolve Rlt_le: real.

Lemma Rgt_ge : forall r1 r2, r1 > r2 -> r1 >= r2.
Proof. now intros r1 r2; left. Qed.

Lemma Rle_ge : forall r1 r2, r1 <= r2 -> r2 >= r1.
Proof. now intros r1 r2 [H1 | H2]; [left | right]. Qed.
#[global]
Hint Immediate Rle_ge: real.
#[global]
Hint Resolve Rle_ge: rorders.

Lemma Rge_le : forall r1 r2, r1 >= r2 -> r2 <= r1.
Proof. now intros r1 r2 [Hge | Heq]; [left | right]. Qed.
#[global]
Hint Resolve Rge_le: real.
#[global]
Hint Immediate Rge_le: rorders.

Lemma Rlt_gt : forall r1 r2, r1 < r2 -> r2 > r1.
Proof. now unfold Rgt. Qed.
#[global]
Hint Resolve Rlt_gt: rorders.

Lemma Rgt_lt : forall r1 r2, r1 > r2 -> r2 < r1.
Proof. now unfold Rgt. Qed.
#[global]
Hint Immediate Rgt_lt: rorders.

Lemma Rnot_le_lt : forall r1 r2, ~ r1 <= r2 -> r2 < r1.
Proof.
  intros r1 r2 r1_nle_r2; destruct (Rtotal_order r1 r2) as [Hlt | [Heq | Hgt]].
  - now exfalso; apply r1_nle_r2; left.
  - now exfalso; apply r1_nle_r2; right.
  - assumption.
Qed.
#[global]
Hint Immediate Rnot_le_lt: real.

Lemma Rnot_ge_gt : forall r1 r2, ~ r1 >= r2 -> r2 > r1.
Proof. now intros r1 r2 H; apply Rnot_le_lt; intros H'%Rle_ge. Qed.

Lemma Rnot_le_gt : forall r1 r2, ~ r1 <= r2 -> r1 > r2.
Proof. now intros r1 r2 H; apply Rnot_le_lt. Qed.

Lemma Rnot_ge_lt : forall r1 r2, ~ r1 >= r2 -> r1 < r2.
Proof. now intros r1 r2 H; apply Rnot_le_lt; intros H'%Rle_ge. Qed.

Lemma Rnot_lt_le : forall r1 r2, ~ r1 < r2 -> r2 <= r1.
Proof.
  intros r1 r2 H; destruct (Rtotal_order r1 r2) as [Hlt | [Heq | Hgt]].
  - now exfalso.
  - now right.
  - now left.
Qed.

Lemma Rnot_gt_le : forall r1 r2, ~ r1 > r2 -> r1 <= r2.
Proof. now intros r1 r2 H; apply Rnot_lt_le. Qed.

Lemma Rnot_gt_ge : forall r1 r2, ~ r1 > r2 -> r2 >= r1.
Proof. now intros r1 r2 H; apply Rle_ge, Rnot_lt_le. Qed.

Lemma Rnot_lt_ge : forall r1 r2, ~ r1 < r2 -> r1 >= r2.
Proof. now intros r1 r2 H; apply Rnot_gt_ge. Qed.

Lemma Rlt_not_le : forall r1 r2, r2 < r1 -> ~ r1 <= r2.
Proof.
  intros r1 r2 Hgt [Hlt | Hle%eq_sym].
  - now apply (Rlt_asym r1 r2).
  - now apply Rlt_not_eq in Hgt.
Qed.
#[global]
Hint Immediate Rlt_not_le: real.

Lemma Rgt_not_le : forall r1 r2, r1 > r2 -> ~ r1 <= r2.
Proof. exact Rlt_not_le. Qed.

Lemma Rlt_not_ge : forall r1 r2, r1 < r2 -> ~ r1 >= r2.
Proof. now intros r1 r2 Hlt%Rlt_not_le Hge%Rge_le. Qed.
#[global]
Hint Immediate Rlt_not_ge: real.

Lemma Rgt_not_ge : forall r1 r2, r2 > r1 -> ~ r1 >= r2.
Proof. exact Rlt_not_ge. Qed.

Lemma Rle_not_lt : forall r1 r2, r2 <= r1 -> ~ r1 < r2.
Proof.
  intros r1 r2 [Hlt | Heq%eq_sym]; intros Hgt.
  - now apply (Rlt_asym r1 r2).
  - now apply Rlt_not_eq in Hgt.
Qed.

Lemma Rge_not_lt : forall r1 r2, r1 >= r2 -> ~ r1 < r2.
Proof. now intros r1 r2 Hge; apply Rle_not_lt, Rge_le. Qed.

Lemma Rle_not_gt : forall r1 r2, r1 <= r2 -> ~ r1 > r2.
Proof. now intros r1 r2 Hle; apply Rle_not_lt. Qed.

Lemma Rge_not_gt : forall r1 r2, r2 >= r1 -> ~ r1 > r2.
Proof. now intros r1 r2 Hge; apply Rge_not_lt. Qed.

(* TODO: We may want to deprecate it but cannot because of the hint used in
   external libs (the stdlib can already be compiled without it) *)
Lemma Req_le_sym : forall r1 r2, r2 = r1 -> r1 <= r2.
Proof. now intros r1 r2; right. Qed.
#[global]
Hint Immediate Req_le_sym: real.

(* TODO: We may want to deprecate it but cannot because of the hint used in
   external libs (the stdlib can already be compiled without it) *)
Lemma Req_ge_sym : forall r1 r2, r2 = r1 -> r1 >= r2.
Proof. now intros r1 r2; right. Qed.
#[global]
Hint Immediate Req_ge_sym: real.

(** *** Asymmetry *)

(** Remark: [Rlt_asym] is in [Raxioms.v] *)

#[export] Instance Rlt_Asymmetric : Asymmetric Rlt | 10 := Rlt_asym.

Lemma Rgt_asym : forall r1 r2, r1 > r2 -> ~ r2 > r1.
Proof. now intros r1 r2; apply Rlt_asym. Qed.

#[export] Instance Rgt_Asymmetric : Asymmetric Rgt | 10 := Rgt_asym.

(** *** Antisymmetry *)

Lemma Rle_antisym : forall r1 r2, r1 <= r2 -> r2 <= r1 -> r1 = r2.
Proof.
  intros r1 r2 [Hlt | Heq] [Hgt | Heq']; try easy.
  now exfalso; apply (Rlt_asym r1 r2).
Qed.
#[global]
Hint Resolve Rle_antisym: real.

#[export] Instance Rle_Antisymmetric : Antisymmetric R eq Rle | 10 := Rle_antisym.

Lemma Rge_antisym : forall r1 r2, r1 >= r2 -> r2 >= r1 -> r1 = r2.
Proof. now intros r1 r2 H1%Rge_le H2%Rge_le; apply Rle_antisym. Qed.

#[export] Instance Rge_Antisymmetric : Antisymmetric R eq Rge | 10 := Rge_antisym.

Lemma Rle_le_eq : forall r1 r2, r1 <= r2 /\ r2 <= r1 <-> r1 = r2.
Proof.
  intros r1 r2; split.
  - now intros [H1 H2]; apply Rle_antisym.
  - now intros ->; split; apply Rle_refl.
Qed.

Lemma Rge_ge_eq : forall r1 r2, r1 >= r2 /\ r2 >= r1 <-> r1 = r2.
Proof.
  intros r1 r2; split.
  - now intros [H1 H2]; apply Rge_antisym.
  - now intros ->; split; apply Rge_refl.
Qed.

(** *** Compatibility with equality *)

Lemma Rlt_eq_compat :
  forall r1 r2 r3 r4, r1 = r2 -> r2 < r4 -> r4 = r3 -> r1 < r3.
Proof. now intros r1 r2 r3 r4 -> Hlt <-. Qed.

Lemma Rgt_eq_compat :
  forall r1 r2 r3 r4, r1 = r2 -> r2 > r4 -> r4 = r3 -> r1 > r3.
Proof. now intros r1 r2 r3 r4 -> Hgt <-. Qed.

(** *** Transitivity *)

(** Remark: [Rlt_trans] is in Raxioms *)
#[export] Instance Rlt_Transitive : Transitive Rlt | 10 := Rlt_trans.

Lemma Rle_trans : forall r1 r2 r3, r1 <= r2 -> r2 <= r3 -> r1 <= r3.
Proof.
  intros r1 r2 r3 [Hlt | ->]; try easy.
  intros [Hlt' | ->].
  - now left; apply (Rlt_trans _ r2).
  - now left.
Qed.

#[export] Instance Rle_Transitive : Transitive Rle | 10 := Rle_trans.

Lemma Rge_trans : forall r1 r2 r3, r1 >= r2 -> r2 >= r3 -> r1 >= r3.
Proof.
  intros r1 r2 r3 H1%Rge_le H2%Rge_le.
  now apply Rle_ge, (Rle_trans _ r2).
Qed.

#[export] Instance Rge_Transitive : Transitive Rge | 10 := Rge_trans.

Lemma Rgt_trans : forall r1 r2 r3, r1 > r2 -> r2 > r3 -> r1 > r3.
Proof. now intros r1 r2 r3 H H'; apply (Rlt_trans _ r2). Qed.

#[export] Instance Rgt_Transitive : Transitive Rgt | 10 := Rgt_trans.

Lemma Rle_lt_trans : forall r1 r2 r3, r1 <= r2 -> r2 < r3 -> r1 < r3.
Proof. now intros r1 r2 r3 [Hlt | ->]; try easy; apply (Rlt_trans _ r2). Qed.

Lemma Rlt_le_trans : forall r1 r2 r3, r1 < r2 -> r2 <= r3 -> r1 < r3.
Proof. now intros r1 r2 r3 H1 [Hlt | ->]; try easy; apply (Rlt_trans _ r2). Qed.

Lemma Rge_gt_trans : forall r1 r2 r3, r1 >= r2 -> r2 > r3 -> r1 > r3.
Proof. now intros r1 r2 r3 H1%Rge_le H2%Rgt_lt; apply (Rlt_le_trans _ r2). Qed.

Lemma Rgt_ge_trans : forall r1 r2 r3, r1 > r2 -> r2 >= r3 -> r1 > r3.
Proof. now intros r1 r2 r3 H1%Rgt_lt H2%Rge_le; apply (Rle_lt_trans _ r2). Qed.

(** *** (Classical) decidability with sumbool types *)

Lemma Rlt_dec : forall r1 r2, {r1 < r2} + {~ r1 < r2}.
Proof.
  intros r1 r2; destruct (total_order_T r1 r2) as [[Hlt | Heq] | Hgt].
  - now left.
  - now right; apply Rge_not_lt; right.
  - now right; apply Rge_not_lt; left.
Qed.

Lemma Rle_dec : forall r1 r2, {r1 <= r2} + {~ r1 <= r2}.
Proof.
  intros r1 r2; destruct (Rlt_dec r2 r1) as [H%Rlt_not_le | H%Rnot_lt_le].
  - now right.
  - now left.
Qed.

Lemma Rgt_dec : forall r1 r2, {r1 > r2} + {~ r1 > r2}.
Proof. now intros r1 r2; apply Rlt_dec. Qed.

Lemma Rge_dec : forall r1 r2, {r1 >= r2} + {~ r1 >= r2}.
Proof.
  intros r1 r2; destruct (Rlt_dec r1 r2) as [H%Rlt_not_ge | H%Rnot_lt_ge].
  - now right.
  - now left.
Qed.

Lemma Rlt_le_dec : forall r1 r2, {r1 < r2} + {r2 <= r1}.
Proof.
  intros r1 r2; destruct (Rlt_dec r1 r2) as [Hlt | H%Rnot_lt_le].
  - now left.
  - now right.
Qed.

Lemma Rlt_ge_dec : forall r1 r2, {r1 < r2} + {r1 >= r2}.
Proof.
  intros r1 r2; destruct (Rlt_le_dec r1 r2) as [Hlt | H%Rle_ge].
  - now left.
  - now right.
Qed.

Lemma Rgt_ge_dec : forall r1 r2, {r1 > r2} + {r2 >= r1}.
Proof.
  intros r1 r2; destruct (Rgt_dec r1 r2) as [Hgt | H%Rnot_gt_ge].
  - now left.
  - now right.
Qed.

Lemma Rgt_le_dec : forall r1 r2, {r1 > r2} + {r1 <= r2}.
Proof.
  intros r1 r2; destruct (Rgt_ge_dec r1 r2) as [Hgt | H%Rge_le].
  - now left.
  - now right.
Qed.

Lemma Rle_lt_dec : forall r1 r2, {r1 <= r2} + {r2 < r1}.
Proof.
  intros r1 r2; destruct (Rle_dec r1 r2) as [Hle | H%Rnot_le_lt].
  - now left.
  - now right.
Qed.

Lemma Rle_gt_dec : forall r1 r2, {r1 <= r2} + {r1 > r2}.
Proof.
  intros r1 r2; destruct (Rle_lt_dec r1 r2) as [Hle | H%Rlt_gt].
  - now left.
  - now right.
Qed.

Lemma Rge_gt_dec : forall r1 r2, {r1 >= r2} + {r2 > r1}.
Proof.
  intros r1 r2; destruct (Rle_dec r2 r1) as [Hle | H%Rnot_le_lt].
  - now left; apply Rle_ge.
  - now right; apply Rlt_gt.
Qed.

Lemma Rge_lt_dec : forall r1 r2, {r1 >= r2} + {r1 < r2}.
Proof.
  intros r1 r2; destruct (Rge_gt_dec r1 r2) as [Hge | H%Rgt_lt].
  - now left.
  - now right.
Qed.

Lemma Rle_lt_or_eq_dec : forall r1 r2, r1 <= r2 -> {r1 < r2} + {r1 = r2}.
Proof.
  intros r1 r2 H; destruct (total_order_T r1 r2) as [[Hlt | Heq] | Hgt].
  - now left.
  - now right.
  - now exfalso; apply (Rgt_not_le r1 r2).
Qed.

Lemma Rge_gt_or_eq_dec : forall r1 r2, r1 >= r2 -> {r1 > r2} + {r1 = r2}.
Proof.
  intros r1 r2 H%Rge_le.
  now destruct (Rle_lt_or_eq_dec r2 r1 H) as [Hle | Heq]; [left | right].
Qed.

(** *** Same theorems with disjunctions instead of sumbools *)

(* TODO: add this to [Init/Specif.v] ? *)
Lemma Private_sumbool_to_or {A B : Prop} : {A} + {B} -> A \/ B.
Proof. now intros [HA | HB]; [left | right]. Qed.

Lemma Rlt_or_not_lt : forall r1 r2, r1 < r2 \/ ~(r1 < r2).
Proof. now intros r1 r2; apply Private_sumbool_to_or, Rlt_dec. Qed.

Lemma Rle_or_not_le : forall r1 r2, r1 <= r2 \/ ~(r1 <= r2).
Proof. now intros r1 r2; apply Private_sumbool_to_or, Rle_dec. Qed.

Lemma Rgt_or_not_gt : forall r1 r2, r1 > r2 \/ ~(r1 > r2).
Proof. now intros r1 r2; apply Private_sumbool_to_or, Rgt_dec. Qed.

Lemma Rge_or_not_ge : forall r1 r2, r1 >= r2 \/ ~(r1 >= r2).
Proof. now intros r1 r2; apply Private_sumbool_to_or, Rge_dec. Qed.

Lemma Rlt_or_le : forall r1 r2, r1 < r2 \/ r2 <= r1.
Proof. now intros r1 r2; apply Private_sumbool_to_or, Rlt_le_dec. Qed.

Lemma Rgt_or_ge : forall r1 r2, r1 > r2 \/ r2 >= r1.
Proof. now intros r1 r2; apply Private_sumbool_to_or, Rgt_ge_dec. Qed.

Lemma Rle_or_lt : forall r1 r2, r1 <= r2 \/ r2 < r1.
Proof. now intros r1 r2; apply Private_sumbool_to_or, Rle_lt_dec. Qed.

Lemma Rge_or_gt : forall r1 r2, r1 >= r2 \/ r2 > r1.
Proof. now intros r1 r2; apply Private_sumbool_to_or, Rge_gt_dec. Qed.

Lemma Rlt_or_ge : forall r1 r2, r1 < r2 \/ r1 >= r2.
Proof. now intros r1 r2; apply Private_sumbool_to_or, Rlt_ge_dec. Qed.

Lemma Rgt_or_le : forall r1 r2, r1 > r2 \/ r1 <= r2.
Proof. now intros r1 r2; apply Private_sumbool_to_or, Rgt_le_dec. Qed.

Lemma Rle_or_gt : forall r1 r2, r1 <= r2 \/ r1 > r2.
Proof. now intros r1 r2; apply Private_sumbool_to_or, Rle_gt_dec. Qed.

Lemma Rge_or_lt : forall r1 r2, r1 >= r2 \/ r1 < r2.
Proof. now intros r1 r2; apply Private_sumbool_to_or, Rge_lt_dec. Qed.

Lemma Rle_lt_or_eq : forall r1 r2, r1 <= r2 -> r1 < r2 \/ r1 = r2.
Proof. now intros r1 r2 H; apply Private_sumbool_to_or, Rle_lt_or_eq_dec. Qed.

Lemma Rge_gt_or_eq : forall r1 r2, r1 >= r2 -> r1 > r2 \/ r1 = r2.
Proof. now intros r1 r2 H; apply Private_sumbool_to_or, Rge_gt_or_eq_dec. Qed.

(*********************************************************)
(** ** Addition                                          *)
(*********************************************************)

Lemma Rplus_eq_compat_l : forall r r1 r2, r1 = r2 -> r + r1 = r + r2.
Proof. now intros r r1 r2 H; f_equal. Qed.

Lemma Rplus_eq_compat_r : forall r r1 r2, r1 = r2 -> r1 + r = r2 + r.
Proof. now intros r r1 r2 H; f_equal. Qed.

(** Remark: the following primitive lemmas are in [Raxioms.v]
    - [Rplus_0_l];
    - [Rplus_comm];
    - [Rplus_opp_r] and
    - [Rplus_assoc] *)

Lemma Rplus_0_r : forall r, r + 0 = r.
Proof. now intros r; rewrite Rplus_comm, Rplus_0_l. Qed.
#[global]
Hint Resolve Rplus_0_r: real.

Lemma Rplus_ne : forall r, r + 0 = r /\ 0 + r = r.
Proof. now intros r; split; [apply Rplus_0_r | apply Rplus_0_l]. Qed.
#[global]
Hint Resolve Rplus_ne: real.

Lemma Rplus_opp_l : forall r, - r + r = 0.
Proof. now intros r; rewrite Rplus_comm; apply Rplus_opp_r. Qed.
#[global]
Hint Resolve Rplus_opp_l: real.

Lemma Rplus_opp_r_uniq : forall r1 r2, r1 + r2 = 0 -> r2 = - r1.
Proof.
  intros r1 r2 H%(Rplus_eq_compat_l (- r1)).
  now rewrite <-Rplus_assoc, Rplus_opp_l, Rplus_0_l, Rplus_0_r in H.
Qed.

Definition f_equal_R := (f_equal (A:=R)).
#[global]
Hint Resolve f_equal_R : real.

Lemma Rplus_eq_reg_l : forall r r1 r2, r + r1 = r + r2 -> r1 = r2.
Proof.
  intros r r1 r2 H%(Rplus_eq_compat_l (- r)).
  now rewrite <-2Rplus_assoc, Rplus_opp_l, 2Rplus_0_l in H.
Qed.
#[global]
Hint Resolve Rplus_eq_reg_l: real.

Lemma Rplus_eq_reg_r : forall r r1 r2, r1 + r = r2 + r -> r1 = r2.
Proof.
  intros r r1 r2 H; rewrite 2(Rplus_comm _ r) in H.
  now apply (Rplus_eq_reg_l r).
Qed.

Lemma Rplus_0_r_uniq : forall r r1, r + r1 = r -> r1 = 0.
Proof. now intros r r1; rewrite <-(Rplus_0_r r) at 2; apply Rplus_eq_reg_l. Qed.

Lemma Rplus_0_l_uniq : forall r r1, r1 + r = r -> r1 = 0.
Proof. now intros r r1; rewrite Rplus_comm; apply Rplus_0_r_uniq. Qed.

(*********************************************************)
(** ** Opposite                                          *)
(*********************************************************)

Lemma Ropp_eq_compat : forall r1 r2, r1 = r2 -> - r1 = - r2.
Proof. now intros r1 r2 H; f_equal. Qed.
#[global]
Hint Resolve Ropp_eq_compat: real.

Lemma Ropp_0 : -0 = 0.
Proof. now apply (Rplus_0_r_uniq 0), Rplus_opp_r. Qed.
#[global]
Hint Resolve Ropp_0: real.

Lemma Ropp_eq_0_compat : forall r, r = 0 -> - r = 0.
Proof. now intros r ->; apply Ropp_0. Qed.
#[global]
Hint Resolve Ropp_eq_0_compat: real.

Lemma Ropp_involutive : forall r, - - r = r.
Proof. now intros r; symmetry; apply (Rplus_opp_r_uniq (- r)), Rplus_opp_l. Qed.
#[global]
Hint Resolve Ropp_involutive: real.

Lemma Ropp_eq_reg : forall r1 r2, - r1 = - r2 -> r1 = r2.
Proof.
  intros r1 r2 H; rewrite <-(Ropp_involutive r1), <-(Ropp_involutive r2).
  now apply Ropp_eq_compat.
Qed.

Lemma Ropp_neq_0_compat : forall r, r <> 0 -> - r <> 0.
Proof.
  intros r H H'%Ropp_eq_compat.
  now rewrite Ropp_involutive, Ropp_0 in H'.
Qed.
#[global]
Hint Resolve Ropp_neq_0_compat: real.

Lemma Ropp_plus_distr : forall r1 r2, - (r1 + r2) = - r1 + - r2.
Proof.
  intros r1 r2; symmetry.
  apply Rplus_opp_r_uniq.
  rewrite (Rplus_comm r1), Rplus_assoc, <-(Rplus_assoc r1), Rplus_opp_r.
  now rewrite Rplus_0_l, Rplus_opp_r.
Qed.
#[global]
Hint Resolve Ropp_plus_distr: real.

(*********************************************************)
(** ** Multiplication                                    *)
(*********************************************************)

Lemma Rmult_eq_compat_l : forall r r1 r2, r1 = r2 -> r * r1 = r * r2.
Proof. now intros r r1 r2 H; f_equal. Qed.

Lemma Rmult_eq_compat_r : forall r r1 r2, r1 = r2 -> r1 * r = r2 * r.
Proof. now intros r r1 r2 H; f_equal. Qed.

(** Remark: the following primitive lemmas are in [Raxioms.v]
    - [Rmult_comm];
    - [Rinv_l];
    - [Rmult_assoc];
    - [Rmult_1_l] and
    - [Rmult_plus_distr_l] *)

Lemma Rinv_r : forall r, r <> 0 -> r * / r = 1.
Proof. now intros r H; rewrite Rmult_comm, Rinv_l. Qed.
#[global]
Hint Resolve Rinv_r: real.


(* TODO: We may want to deprecate it but cannot because of the hint used in
   external libs (the stdlib can already be compiled without it) *)
Lemma Rinv_l_sym : forall r, r <> 0 -> 1 = / r * r.
Proof. now intros r H; symmetry; apply Rinv_l. Qed.
#[global]
Hint Resolve Rinv_l_sym: real.

(* TODO: We may want to deprecate it but cannot because of the hint used in
   external libs (the stdlib can already be compiled without it) *)
Lemma Rinv_r_sym : forall r, r <> 0 -> 1 = r * / r.
Proof. now intros r H; symmetry; apply Rinv_r. Qed.
#[global]
Hint Resolve Rinv_r_sym: real.

(* For consistency with Rplus_opp_r and Rplus_opp_l. *)
Definition Rmult_inv_r := Rinv_r.
Definition Rmult_inv_l := Rinv_l.

Lemma Rmult_1_r : forall r, r * 1 = r.
Proof. now intros r; rewrite Rmult_comm, Rmult_1_l. Qed.
#[global]
Hint Resolve Rmult_1_r: real.

Lemma Rmult_ne : forall r, r * 1 = r /\ 1 * r = r.
Proof. now intros r; split; [apply Rmult_1_r | apply Rmult_1_l]. Qed.
#[global]
Hint Resolve Rmult_ne: real.

Lemma Rmult_eq_reg_l : forall r r1 r2, r * r1 = r * r2 -> r <> 0 -> r1 = r2.
Proof.
  intros r r1 r2 H r_not_0.
  apply (Rmult_eq_compat_l (/ r)) in H.
  now rewrite <-2Rmult_assoc, Rinv_l, 2Rmult_1_l in H.
Qed.

Lemma Rmult_eq_reg_r : forall r r1 r2, r1 * r = r2 * r -> r <> 0 -> r1 = r2.
Proof.
  intros r r1 r2 H1 H2.
  apply Rmult_eq_reg_l with (2 := H2).
  now rewrite 2!(Rmult_comm r).
Qed.

Lemma Rmult_plus_distr_r :
  forall r1 r2 r3, (r1 + r2) * r3 = r1 * r3 + r2 * r3.
Proof.
  intros r1 r2 r3.
  now rewrite 3(Rmult_comm _ r3); apply Rmult_plus_distr_l.
Qed.

Lemma Rmult_0_r : forall r, r * 0 = 0.
Proof.
  intros r; apply (Rplus_eq_reg_l r).
  rewrite <-(Rmult_1_r r) at 1; rewrite <-Rmult_plus_distr_l.
  now rewrite 2Rplus_0_r, Rmult_1_r.
Qed.
#[global]
Hint Resolve Rmult_0_r: real.

Lemma Rmult_0_l : forall r, 0 * r = 0.
Proof. now intros r; rewrite Rmult_comm, Rmult_0_r. Qed.
#[global]
Hint Resolve Rmult_0_l: real.

Lemma Rmult_integral : forall r1 r2, r1 * r2 = 0 -> r1 = 0 \/ r2 = 0.
Proof.
  intros; destruct (Req_dec r1 0) as [Hz | Hnz]; [left | right]; try easy.
  apply (Rmult_eq_compat_l (/ r1)) in H.
  now rewrite <-Rmult_assoc, Rinv_l, Rmult_1_l, Rmult_0_r in H.
Qed.

Lemma Rmult_eq_0_compat : forall r1 r2, r1 = 0 \/ r2 = 0 -> r1 * r2 = 0.
Proof. now intros r1 r2 [-> | ->]; [apply Rmult_0_l | apply Rmult_0_r]. Qed.
#[global]
Hint Resolve Rmult_eq_0_compat: real.

Lemma Rmult_eq_0_compat_r : forall r1 r2, r1 = 0 -> r1 * r2 = 0.
Proof. now intros r1 r2 ->; apply Rmult_0_l. Qed.

Lemma Rmult_eq_0_compat_l : forall r1 r2, r2 = 0 -> r1 * r2 = 0.
Proof. now intros r1 r2 ->; apply Rmult_0_r. Qed.

Lemma Rmult_neq_0_reg : forall r1 r2, r1 * r2 <> 0 -> r1 <> 0 /\ r2 <> 0.
Proof.
  intros r1 r2 H; split; intros Heq0; rewrite Heq0 in H.
  - now rewrite Rmult_0_l in H.
  - now rewrite Rmult_0_r in H.
Qed.

Lemma Rmult_integral_contrapositive :
  forall r1 r2, r1 <> 0 /\ r2 <> 0 -> r1 * r2 <> 0.
Proof. now intros r1 r2 [H1 H2] [r10 | r20]%Rmult_integral. Qed.
#[global]
Hint Resolve Rmult_integral_contrapositive: real.

Lemma Rmult_integral_contrapositive_currified :
  forall r1 r2, r1 <> 0 -> r2 <> 0 -> r1 * r2 <> 0.
Proof. now intros r1 r2 H1 H2; apply Rmult_integral_contrapositive. Qed.

(*********************************************************)
(** ** Opposite and multiplication                       *)
(*********************************************************)

Lemma Ropp_mult_distr_l : forall r1 r2, - (r1 * r2) = - r1 * r2.
Proof.
  intros r1 r2; symmetry; apply Rplus_opp_r_uniq.
  now rewrite <-Rmult_plus_distr_r, Rplus_opp_r, Rmult_0_l.
Qed.

Lemma Ropp_mult_distr_r : forall r1 r2, - (r1 * r2) = r1 * - r2.
Proof. now intros r1 r2; rewrite 2(Rmult_comm r1); apply Ropp_mult_distr_l. Qed.

Lemma Ropp_mult_distr_l_reverse : forall r1 r2, - r1 * r2 = - (r1 * r2).
Proof. now intros r1 r2; symmetry; apply Ropp_mult_distr_l. Qed.
#[global]
Hint Resolve Ropp_mult_distr_l_reverse: real.

Lemma Rmult_opp_opp : forall r1 r2, - r1 * - r2 = r1 * r2.
Proof.
  intros r1 r2.
  now rewrite <-Ropp_mult_distr_l, <-Ropp_mult_distr_r, Ropp_involutive.
Qed.
#[global]
Hint Resolve Rmult_opp_opp: real.

Lemma Ropp_mult_distr_r_reverse : forall r1 r2, r1 * - r2 = - (r1 * r2).
Proof. now intros r1 r2; symmetry; apply Ropp_mult_distr_r. Qed.

(*********************************************************)
(** ** Subtraction                                       *)
(*********************************************************)

Lemma Rminus_def : forall r1 r2, r1 - r2 = r1 + - r2.
Proof. now unfold Rminus. Qed.

Lemma Rminus_eq_compat_l : forall r r1 r2, r1 = r2 -> r - r1 = r - r2.
Proof.
  now unfold Rminus; intros r r1 r2 H%Ropp_eq_compat; apply Rplus_eq_compat_l.
Qed.

Lemma Rminus_eq_compat_r : forall r r1 r2, r1 = r2 -> r1 - r = r2 - r.
Proof. now unfold Rminus; intros r r1 r2;apply Rplus_eq_compat_r. Qed.

Lemma Rminus_eq_reg_l : forall r r1 r2, r - r1 = r - r2 -> r1 = r2.
Proof.
  now unfold Rminus; intros r r1 r2 H%Rplus_eq_reg_l; apply Ropp_eq_reg.
Qed.

Lemma Rminus_eq_reg_r : forall r r1 r2, r1 - r = r2 - r -> r1 = r2.
Proof. now unfold Rminus; intros r r1 r2; apply Rplus_eq_reg_r. Qed.

Lemma Rminus_0_r : forall r, r - 0 = r.
Proof. now unfold Rminus; intros r; rewrite Ropp_0, Rplus_0_r. Qed.
#[global]
Hint Resolve Rminus_0_r: real.

Lemma Rminus_0_l : forall r, 0 - r = - r.
Proof. now unfold Rminus; intros r; rewrite Rplus_0_l. Qed.
#[global]
Hint Resolve Rminus_0_l: real.

Lemma Ropp_minus_distr : forall r1 r2, - (r1 - r2) = r2 - r1.
Proof.
  unfold Rminus; intros r1 r2.
  now rewrite Ropp_plus_distr, Ropp_involutive, Rplus_comm.
Qed.
#[global]
Hint Resolve Ropp_minus_distr: real.

Lemma Rminus_diag_eq : forall r1 r2, r1 = r2 -> r1 - r2 = 0.
Proof. now unfold Rminus; intros r1 r2 ->; rewrite Rplus_opp_r. Qed.
#[global]
Hint Resolve Rminus_diag_eq: real.

Lemma Rminus_diag : forall r, r - r = 0.
Proof. now intros r; apply Rminus_diag_eq. Qed.

Lemma Rminus_diag_uniq : forall r1 r2, r1 - r2 = 0 -> r1 = r2.
Proof.
  unfold Rminus; intros r1 r2 H%(Rplus_eq_compat_r r2).
  now rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_l, Rplus_0_r in H.
Qed.
#[global]
Hint Immediate Rminus_diag_uniq: real.

(* TODO: We may want to deprecate it but cannot because of the hint used in
   external libs (the stdlib can already be compiled without it) *)
Lemma Rminus_diag_uniq_sym : forall r1 r2, r2 - r1 = 0 -> r1 = r2.
Proof. now intros r1 r2; symmetry;apply Rminus_diag_uniq. Qed.
#[global]
Hint Immediate Rminus_diag_uniq_sym: real.


Lemma Rplus_minus : forall r1 r2, r1 + (r2 - r1) = r2.
Proof.
  unfold Rminus; intros r1 r2.
  now rewrite Rplus_comm, Rplus_assoc, Rplus_opp_l, Rplus_0_r.
Qed.
#[global]
Hint Resolve Rplus_minus: real.

Lemma Rminus_eq_contra : forall r1 r2, r1 <> r2 -> r1 - r2 <> 0.
Proof. now intros r1 r2 H H0%Rminus_diag_uniq. Qed.
#[global]
Hint Resolve Rminus_eq_contra: real.

Lemma Rminus_not_eq : forall r1 r2, r1 - r2 <> 0 -> r1 <> r2.
Proof. now intros r1 r2 H Heq; apply H, Rminus_diag_eq. Qed.
#[global]
Hint Resolve Rminus_not_eq: real.

(* TODO: We may want to deprecate it but cannot because of the hint used in
   external libs (the stdlib can already be compiled without it) *)
Lemma Rminus_not_eq_right : forall r1 r2, r2 - r1 <> 0 -> r1 <> r2.
Proof. now intros r1 r2 H; apply not_eq_sym, Rminus_not_eq. Qed.
#[global]
Hint Resolve Rminus_not_eq_right: real.

Lemma Rmult_minus_distr_l :
  forall r1 r2 r3, r1 * (r2 - r3) = r1 * r2 - r1 * r3.
Proof.
  unfold Rminus; intros r1 r2 r3; rewrite Rmult_plus_distr_l.
  now rewrite Ropp_mult_distr_r.
Qed.

Lemma Rmult_minus_distr_r :
  forall r1 r2 r3, (r2 - r3) * r1 = r2 * r1 - r3 * r1.
Proof.
  intros r1 r2 r3; rewrite 3(Rmult_comm _ r1).
  now apply Rmult_minus_distr_l.
Qed.

Lemma Rplus_minus_r : forall r1 r2, r1 + r2 - r2 = r1.
Proof.
  now intros r1 r2; unfold Rminus; rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
Qed.

Lemma Rplus_minus_l : forall r1 r2, r1 + r2 - r1 = r2.
Proof. now intros r1 r2; rewrite Rplus_comm, Rplus_minus_r. Qed.

Lemma Rplus_minus_assoc : forall r1 r2 r3, r1 + (r2 - r3) = (r1 + r2) - r3.
Proof. now unfold Rminus; intros r1 r2 r3; rewrite Rplus_assoc. Qed.

Lemma Rplus_minus_swap : forall r1 r2 r3, (r1 + r2) - r3 = (r1 - r3) + r2.
Proof.
  unfold Rminus; intros r1 r2 r3.
  now rewrite Rplus_assoc, (Rplus_comm r2), <-Rplus_assoc.
Qed.

Lemma Rminus_plus_distr : forall r1 r2 r3, r1 - (r2 + r3) = (r1 - r2) - r3.
Proof.
  now unfold Rminus; intros r1 r2 r3; rewrite Ropp_plus_distr, Rplus_assoc.
Qed.

Lemma Rminus_plus_r_r : forall r r1 r2, (r1 + r) - (r2 + r) = r1 - r2.
Proof.
  intros r r1 r2; rewrite Rminus_plus_distr, Rplus_comm.
  now rewrite <-Rplus_minus_assoc, Rplus_minus_l.
Qed.

Lemma Rminus_plus_l_r : forall r r1 r2, (r + r1) - (r2 + r) = r1 - r2.
Proof. now intros r r1 r2; rewrite (Rplus_comm r), Rminus_plus_r_r. Qed.

Lemma Rminus_plus_r_l : forall r r1 r2, (r1 + r) - (r + r2) = r1 - r2.
Proof. now intros r r1 r2; rewrite (Rplus_comm r), Rminus_plus_r_r. Qed.

Lemma Rminus_plus_l_l : forall r r1 r2, (r + r1) - (r + r2) = r1 - r2.
Proof. now intros r r1 r2; rewrite (Rplus_comm _ r1), Rminus_plus_r_l. Qed.

(*********************************************************)
(** ** Inverse                                           *)
(*********************************************************)

Lemma Rinv_0 : / 0 = 0.
Proof.
  rewrite RinvImpl.Rinv_def.
  destruct (Req_appart_dec 0 R0) as [eq0 | [lt0 | gt0]]; try easy;
  now exfalso; apply (Rlt_irrefl 0).
Qed.

Lemma Rmult_inv_r_uniq :
  forall r1 r2, r1 <> 0 -> r1 * r2 = 1 -> r2 = / r1.
Proof.
  intros r1 r2 Hn0 H%(Rmult_eq_compat_l (/ r1)).
  now rewrite <-Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l in H.
Qed.

Lemma Rinv_eq_compat : forall r1 r2, r1 = r2 -> / r1 = / r2.
Proof. now intros r1 r2 H; f_equal. Qed.

Lemma Rinv_1 : / 1 = 1.
Proof.
  symmetry; apply Rmult_inv_r_uniq.
  - exact R1_neq_R0.
  - now rewrite Rmult_1_r.
Qed.
#[global]
Hint Resolve Rinv_1: real.

Lemma Rinv_neq_0_compat : forall r, r <> 0 -> / r <> 0.
Proof.
  intros r H H'; apply R1_neq_R0.
  now rewrite <-(Rinv_l r), H', Rmult_0_l.
Qed.
#[global]
Hint Resolve Rinv_neq_0_compat: real.

Lemma Rinv_inv r : / / r = r.
Proof.
destruct (Req_dec r 0) as [-> | H].
- now rewrite Rinv_0, Rinv_0.
- symmetry; apply Rmult_inv_r_uniq.
  * now apply Rinv_neq_0_compat.
  * now rewrite Rinv_l.
Qed.
#[global]
Hint Resolve Rinv_inv: real.

Lemma Rinv_eq_reg : forall r1 r2, / r1 = / r2 -> r1 = r2.
Proof. now intros r1 r2 H%Rinv_eq_compat; rewrite !Rinv_inv in H. Qed.

Lemma Rinv_mult r1 r2 : / (r1 * r2) = / r1 * / r2.
Proof.
destruct (Req_dec r1 0) as [-> | H1].
- now rewrite Rinv_0, 2!Rmult_0_l, Rinv_0.
- destruct (Req_dec r2 0) as [-> | H2].
  + now rewrite Rinv_0, 2!Rmult_0_r, Rinv_0.
  + symmetry; apply Rmult_inv_r_uniq.
    { now apply Rmult_integral_contrapositive_currified. }
    rewrite (Rmult_comm r1), Rmult_assoc, <-(Rmult_assoc r1).
    now rewrite Rinv_r, Rmult_1_l, Rinv_r.
Qed.

Lemma Rinv_opp r : / - r = - / r.
Proof.
  destruct (Req_dec r 0) as [-> | H].
  - now rewrite Ropp_0, Rinv_0, Ropp_0.
  - symmetry; apply Rmult_inv_r_uniq.
    { now apply Ropp_neq_0_compat. }
    now rewrite Rmult_opp_opp, Rinv_r.
Qed.

Lemma Rmult_inv_m_id_r : forall r1 r2, r1 <> 0 -> r1 * / r1 * r2 = r2.
Proof. now intros r1 r2 r1n0; rewrite Rinv_r, Rmult_1_l. Qed.

Lemma Rmult_inv_r_id_l : forall r1 r2, r1 <> 0 -> r2 * r1 * / r1 = r2.
Proof. now intros r1 r2 r1n0; rewrite Rmult_assoc, Rinv_r, Rmult_1_r. Qed.

Lemma Rmult_inv_r_id_m : forall r1 r2, r1 <> 0 -> r1 * r2 * / r1 = r2.
Proof. now intros r1 r2 r1n0; rewrite (Rmult_comm r1), Rmult_inv_r_id_l. Qed.
#[global]
Hint Resolve Rmult_inv_m_id_r Rmult_inv_r_id_l Rmult_inv_r_id_m: real.


(*********************************************************)
(** ** Square function                                   *)
(*********************************************************)

Definition Rsqr r : R := r * r.
Notation "r ²" := (Rsqr r) (at level 1, format "r ²") : R_scope.

(* Useful to fold Rsqr *)
Lemma Rsqr_def : forall r, r² = r * r.
Proof. now unfold Rsqr; intros r. Qed.

Lemma Rsqr_0 : Rsqr 0 = 0.
Proof. now unfold Rsqr; apply Rmult_0_r. Qed.

Lemma Rsqr_0_uniq : forall r, Rsqr r = 0 -> r = 0.
Proof. now unfold Rsqr; intros r [-> | ->]%Rmult_integral. Qed.

(*********************************************************)
(** ** Order and addition                                *)
(*********************************************************)

(** *** Compatibility *)

(** Remark: [Rplus_lt_compat_l] is in [Raxioms.v] *)

Lemma Rplus_gt_compat_l : forall r r1 r2, r1 > r2 -> r + r1 > r + r2.
Proof. now intros r r1 r2; apply Rplus_lt_compat_l. Qed.
#[global]
Hint Resolve Rplus_gt_compat_l: real.

Lemma Rplus_lt_compat_r : forall r r1 r2, r1 < r2 -> r1 + r < r2 + r.
Proof.
  intros r r1 r2 r1_lt_r2; rewrite (Rplus_comm r1), (Rplus_comm r2).
  now apply Rplus_lt_compat_l.
Qed.
#[global]
Hint Resolve Rplus_lt_compat_r: real.

Lemma Rplus_gt_compat_r : forall r r1 r2, r1 > r2 -> r1 + r > r2 + r.
Proof. now intros r r1 r2; apply Rplus_lt_compat_r. Qed.

Lemma Rplus_le_compat_l : forall r r1 r2, r1 <= r2 -> r + r1 <= r + r2.
Proof.
  unfold Rle; intros r r1 r2 [Hlt | ->].
  - now left; apply Rplus_lt_compat_l.
  - now right.
Qed.

Lemma Rplus_ge_compat_l : forall r r1 r2, r1 >= r2 -> r + r1 >= r + r2.
Proof. now intros r r1 r2 H%Rge_le; apply Rle_ge, Rplus_le_compat_l. Qed.
#[global]
Hint Resolve Rplus_ge_compat_l: real.

Lemma Rplus_le_compat_r : forall r r1 r2, r1 <= r2 -> r1 + r <= r2 + r.
Proof.
  intros r r1 r2 H.
  now rewrite 2(Rplus_comm _ r); apply Rplus_le_compat_l.
Qed.

#[global]
Hint Resolve Rplus_le_compat_l Rplus_le_compat_r: real.

Lemma Rplus_ge_compat_r : forall r r1 r2, r1 >= r2 -> r1 + r >= r2 + r.
Proof. now intros r r1 r2 H%Rge_le; apply Rle_ge, Rplus_le_compat_r. Qed.

Lemma Rplus_lt_compat :
  forall r1 r2 r3 r4, r1 < r2 -> r3 < r4 -> r1 + r3 < r2 + r4.
Proof.
  intros r1 r2 r3 r4 r1_lt_r2 r3_lt_r4; apply (Rlt_trans _ (r2 + r3)).
  - now apply Rplus_lt_compat_r.
  - now apply Rplus_lt_compat_l.
Qed.
#[global]
Hint Immediate Rplus_lt_compat: real.

Lemma Rplus_le_compat :
  forall r1 r2 r3 r4, r1 <= r2 -> r3 <= r4 -> r1 + r3 <= r2 + r4.
Proof.
  intros r1 r2 r3 r4 r1_lt_r2 r3_lt_r4; apply (Rle_trans _ (r2 + r3)).
  - now apply Rplus_le_compat_r.
  - now apply Rplus_le_compat_l.
Qed.
#[global]
Hint Immediate Rplus_le_compat: real.

Lemma Rplus_gt_compat :
  forall r1 r2 r3 r4, r1 > r2 -> r3 > r4 -> r1 + r3 > r2 + r4.
Proof. now intros r1 r2 r3 r4; apply Rplus_lt_compat. Qed.

Lemma Rplus_ge_compat :
  forall r1 r2 r3 r4, r1 >= r2 -> r3 >= r4 -> r1 + r3 >= r2 + r4.
Proof.
  now intros r1 r2 r3 r4 H1%Rge_le H2%Rge_le; apply Rle_ge, Rplus_le_compat.
Qed.

Lemma Rplus_lt_le_compat :
  forall r1 r2 r3 r4, r1 < r2 -> r3 <= r4 -> r1 + r3 < r2 + r4.
Proof.
  intros r1 r2 r3 r4 Hlt Hle; apply (Rlt_le_trans _ (r2 + r3)).
  - now apply Rplus_lt_compat_r.
  - now apply Rplus_le_compat_l.
Qed.

Lemma Rplus_le_lt_compat :
  forall r1 r2 r3 r4, r1 <= r2 -> r3 < r4 -> r1 + r3 < r2 + r4.
Proof.
  intros r1 r2 r3 r4 H H'; rewrite (Rplus_comm r1), (Rplus_comm r2).
  now apply Rplus_lt_le_compat.
Qed.
#[global]
Hint Immediate Rplus_lt_le_compat Rplus_le_lt_compat: real.

Lemma Rplus_gt_ge_compat :
  forall r1 r2 r3 r4, r1 > r2 -> r3 >= r4 -> r1 + r3 > r2 + r4.
Proof. now intros r1 r2 r3 r4 H H'%Rge_le; apply Rplus_lt_le_compat. Qed.

Lemma Rplus_ge_gt_compat :
  forall r1 r2 r3 r4, r1 >= r2 -> r3 > r4 -> r1 + r3 > r2 + r4.
Proof. now intros r1 r2 r3 r4 H%Rge_le H'; apply Rplus_le_lt_compat. Qed.

Lemma Rplus_lt_0_compat : forall r1 r2, 0 < r1 -> 0 < r2 -> 0 < r1 + r2.
Proof.
  now intros r1 r2 I I'; rewrite <-(Rplus_0_r 0); apply Rplus_lt_compat.
Qed.

Lemma Rplus_le_lt_0_compat : forall r1 r2, 0 <= r1 -> 0 < r2 -> 0 < r1 + r2.
Proof.
  now intros r1 r2 I I'; rewrite <-(Rplus_0_r 0); apply Rplus_le_lt_compat.
Qed.

Lemma Rplus_lt_le_0_compat : forall r1 r2, 0 < r1 -> 0 <= r2 -> 0 < r1 + r2.
Proof.
  now intros r1 r2 I I'; rewrite <-(Rplus_0_r 0); apply Rplus_lt_le_compat.
Qed.

Lemma Rplus_le_le_0_compat : forall r1 r2, 0 <= r1 -> 0 <= r2 -> 0 <= r1 + r2.
Proof.
  now intros r1 r2 I I'; rewrite <-(Rplus_0_r 0); apply Rplus_le_compat.
Qed.

Lemma Rplus_eq_0_l :
  forall r1 r2, 0 <= r1 -> 0 <= r2 -> r1 + r2 = 0 -> r1 = 0.
Proof.
  intros r1 r2 [Hlt | <-]; try easy.
  intros [Hlt' | <-] H.
  - exfalso; apply (Rgt_not_eq (r1 + r2) 0); try easy.
    now rewrite <-(Rplus_0_r 0); apply Rplus_lt_compat.
  - now rewrite Rplus_0_r in H.
Qed.

Lemma Rplus_eq_0 :
  forall r1 r2, 0 <= r1 -> 0 <= r2 -> r1 + r2 = 0 -> r1 = 0 /\ r2 = 0.
Proof.
  intros r1 r2 H1 H2 Hp; split.
  - now apply (Rplus_eq_0_l _ r2).
  - now rewrite Rplus_comm in Hp; apply (Rplus_eq_0_l r2 r1).
Qed.

(** *** Cancellation *)

Lemma Rplus_lt_reg_l : forall r r1 r2, r + r1 < r + r2 -> r1 < r2.
Proof.
  intros r r1 r2 H%(Rplus_lt_compat_l (-r)).
  now rewrite <-2Rplus_assoc, Rplus_opp_l, 2Rplus_0_l in H.
Qed.

Lemma Rplus_lt_reg_r : forall r r1 r2, r1 + r < r2 + r -> r1 < r2.
Proof.
  intros r r1 r2 H.
  rewrite (Rplus_comm r1), (Rplus_comm r2) in H.
  now apply (Rplus_lt_reg_l r).
Qed.

Lemma Rplus_le_reg_l : forall r r1 r2, r + r1 <= r + r2 -> r1 <= r2.
Proof.
  intros r r1 r2 [Ilt | Eq].
  - left; apply (Rplus_lt_reg_l r r1 r2 Ilt).
  - right; apply (Rplus_eq_reg_l r r1 r2 Eq).
Qed.

Lemma Rplus_le_reg_r : forall r r1 r2, r1 + r <= r2 + r -> r1 <= r2.
Proof.
  intros r r1 r2 H.
  now apply (Rplus_le_reg_l r); rewrite 2(Rplus_comm r).
Qed.

Lemma Rplus_gt_reg_l : forall r r1 r2, r + r1 > r + r2 -> r1 > r2.
Proof. now intros r r1 r2 H; apply (Rplus_lt_reg_l r r2 r1 H). Qed.

Lemma Rplus_gt_reg_r : forall r r1 r2, r1 + r > r2 + r -> r1 > r2.
Proof. now intros r r1 r2 H; apply (Rplus_lt_reg_r r r2 r1 H). Qed.

Lemma Rplus_ge_reg_l : forall r r1 r2, r + r1 >= r + r2 -> r1 >= r2.
Proof. now intros r r1 r2 H%Rge_le; apply Rle_ge, (Rplus_le_reg_l r). Qed.

Lemma Rplus_ge_reg_r : forall r r1 r2, r1 + r >= r2 + r -> r1 >= r2.
Proof. now intros r r1 r2 H%Rge_le; apply Rle_ge, (Rplus_le_reg_r r). Qed.

Lemma Rplus_le_reg_pos_r :
  forall r1 r2 r3, 0 <= r2 -> r1 + r2 <= r3 -> r1 <= r3.
Proof.
  intros r1 r2 r3 H H'.
  apply (Rle_trans _ (r1 + r2)); try easy.
  now rewrite <-(Rplus_0_r r1) at 1; apply Rplus_le_compat_l.
Qed.

Lemma Rplus_lt_reg_pos_r : forall r1 r2 r3, 0 <= r2 -> r1 + r2 < r3 -> r1 < r3.
Proof.
  intros r1 r2 r3 H H'.
  apply (Rle_lt_trans _ (r1 + r2)); try easy.
  now rewrite <-(Rplus_0_r r1) at 1; apply Rplus_le_compat_l.
Qed.

Lemma Rplus_ge_reg_neg_r :
  forall r1 r2 r3, 0 >= r2 -> r1 + r2 >= r3 -> r1 >= r3.
Proof.
  intros r1 r2 r3 H H'.
  apply (Rge_trans _ (r1 + r2)); try easy.
  now rewrite <-(Rplus_0_r r1) at 1; apply Rplus_ge_compat_l.
Qed.

Lemma Rplus_gt_reg_neg_r : forall r1 r2 r3, 0 >= r2 -> r1 + r2 > r3 -> r1 > r3.
Proof.
  intros r1 r2 r3 H H'.
  apply (Rge_gt_trans _ (r1 + r2)); try easy.
  now rewrite <-(Rplus_0_r r1) at 1; apply Rplus_ge_compat_l.
Qed.

Lemma Rplus_le_lt_0_neq_0 : forall r1 r2, 0 <= r1 -> 0 < r2 -> r1 + r2 <> 0.
Proof.
  intros r1 r2 H1 H2; apply not_eq_sym, Rlt_not_eq.
  now rewrite <-(Rplus_0_l 0); apply Rplus_le_lt_compat.
Qed.
#[global]
Hint Immediate Rplus_le_lt_0_neq_0: real.

(** *** Comparison of addition with left operand *)

Lemma Rplus_pos_gt : forall r1 r2, r2 > 0 -> r1 + r2 > r1.
Proof.
  now intros r1 r2 H; rewrite <-(Rplus_0_r r1) at 2; apply Rplus_gt_compat_l.
Qed.

Lemma Rplus_nneg_ge : forall r1 r2, r2 >= 0 -> r1 + r2 >= r1.
Proof.
  now intros r1 r2 H; rewrite <-(Rplus_0_r r1) at 2; apply Rplus_ge_compat_l.
Qed.

Lemma Rplus_neg_lt : forall r1 r2, r2 < 0 -> r1 + r2 < r1.
Proof.
  now intros r1 r2 H; rewrite <-(Rplus_0_r r1) at 2; apply Rplus_lt_compat_l.
Qed.

Lemma Rplus_npos_le : forall r1 r2, r2 <= 0 -> r1 + r2 <= r1.
Proof.
  now intros r1 r2 H; rewrite <-(Rplus_0_r r1) at 2; apply Rplus_le_compat_l.
Qed.

(** *** Sign of addition *)

Lemma Rplus_pos_pos : forall r1 r2, r1 > 0 -> r2 > 0 -> r1 + r2 > 0.
Proof. now intros r1 r2; apply Rplus_lt_0_compat. Qed.

Lemma Rplus_neg_neg : forall r1 r2, r1 < 0 -> r2 < 0 -> r1 + r2 < 0.
Proof.
  now intros r1 r2 H1 H2; rewrite <-(Rplus_0_l 0); apply Rplus_lt_compat.
Qed.

Lemma Rplus_nneg_nneg : forall r1 r2, r1 >= 0 -> r2 >= 0 -> r1 + r2 >= 0.
Proof.
  now intros r1 r2 H1 H2; rewrite <-(Rplus_0_l 0); apply Rplus_ge_compat.
Qed.

Lemma Rplus_npos_npos : forall r1 r2, r1 <= 0 -> r2 <= 0 -> r1 + r2 <= 0.
Proof.
  now intros r1 r2 H1 H2; rewrite <-(Rplus_0_l 0); apply Rplus_le_compat.
Qed.

Lemma Rplus_pos_nneg : forall r1 r2, r1 > 0 -> r2 >= 0 -> r1 + r2 > 0.
Proof.
  now intros r1 r2 H1 H2; rewrite <-(Rplus_0_l 0); apply Rplus_gt_ge_compat.
Qed.

Lemma Rplus_nneg_pos : forall r1 r2, r1 >= 0 -> r2 > 0 -> r1 + r2 > 0.
Proof.
  now intros r1 r2 H1 H2; rewrite <-(Rplus_0_l 0); apply Rplus_ge_gt_compat.
Qed.

Lemma Rplus_neg_npos : forall r1 r2, r1 < 0 -> r2 <= 0 -> r1 + r2 < 0.
Proof.
  now intros r1 r2 H1 H2; rewrite <-(Rplus_0_l 0); apply Rplus_lt_le_compat.
Qed.

Lemma Rplus_npos_neg : forall r1 r2, r1 <= 0 -> r2 < 0 -> r1 + r2 < 0.
Proof.
  now intros r1 r2 H1 H2; rewrite <-(Rplus_0_l 0); apply Rplus_le_lt_compat.
Qed.

(*********************************************************)
(** ** Order and opposite                                *)
(*********************************************************)

(** *** Contravariant compatibility *)

Lemma Ropp_gt_lt_contravar : forall r1 r2, r1 > r2 -> - r1 < - r2.
Proof.
  intros r1 r2 H.
  apply (Rplus_lt_reg_l r1), (Rplus_lt_reg_r r2).
  now rewrite Rplus_opp_r, Rplus_0_l, Rplus_assoc, Rplus_opp_l, Rplus_0_r.
Qed.
#[global]
(* TODO: why core? *)
Hint Resolve Ropp_gt_lt_contravar : core.

Lemma Ropp_lt_gt_contravar : forall r1 r2, r1 < r2 -> - r1 > - r2.
Proof. now intros r1 r2 H; apply Ropp_gt_lt_contravar. Qed.
#[global]
Hint Resolve Ropp_lt_gt_contravar: real.

Lemma Ropp_lt_contravar : forall r1 r2, r2 < r1 -> - r1 < - r2.
Proof. now intros r1 r2; apply Ropp_lt_gt_contravar. Qed.
#[global]
Hint Resolve Ropp_lt_contravar: real.

Lemma Ropp_gt_contravar : forall r1 r2, r2 > r1 -> - r1 > - r2.
Proof. now intros r1 r2; apply Ropp_lt_gt_contravar. Qed.

Lemma Ropp_le_ge_contravar : forall r1 r2, r1 <= r2 -> - r1 >= - r2.
Proof.
  now intros r1 r2 [I | ->]; [left | right; easy]; apply Ropp_lt_contravar.
Qed.
#[global]
Hint Resolve Ropp_le_ge_contravar: real.

Lemma Ropp_ge_le_contravar : forall r1 r2, r1 >= r2 -> - r1 <= - r2.
Proof. now intros r1 r2 I%Rge_le; apply Rge_le, Ropp_le_ge_contravar. Qed.
#[global]
Hint Resolve Ropp_ge_le_contravar: real.

Lemma Ropp_le_contravar : forall r1 r2, r2 <= r1 -> - r1 <= - r2.
Proof. now intros r1 r2 I; apply Rge_le, Ropp_le_ge_contravar. Qed.
#[global]
Hint Resolve Ropp_le_contravar: real.

Lemma Ropp_ge_contravar : forall r1 r2, r2 >= r1 -> - r1 >= - r2.
Proof. now intros r1 r2 I; apply Rle_ge, Ropp_ge_le_contravar. Qed.

Lemma Ropp_0_lt_gt_contravar : forall r, 0 < r -> 0 > - r.
Proof. now intros r I; rewrite <-Ropp_0; apply Ropp_lt_contravar. Qed.
#[global]
Hint Resolve Ropp_0_lt_gt_contravar: real.

Lemma Ropp_0_gt_lt_contravar : forall r, 0 > r -> 0 < - r.
Proof. now intros r I; rewrite <-Ropp_0; apply Ropp_lt_contravar. Qed.
#[global]
Hint Resolve Ropp_0_gt_lt_contravar: real.

Lemma Ropp_lt_gt_0_contravar : forall r, r > 0 -> - r < 0.
Proof. now intros r I; rewrite <-Ropp_0; apply Ropp_lt_contravar. Qed.
#[global]
Hint Resolve Ropp_lt_gt_0_contravar: real.

Lemma Ropp_gt_lt_0_contravar : forall r, r < 0 -> - r > 0.
Proof. now intros r I; rewrite <-Ropp_0; apply Ropp_lt_contravar. Qed.
#[global]
Hint Resolve Ropp_gt_lt_0_contravar: real.

Lemma Ropp_0_le_ge_contravar : forall r, 0 <= r -> 0 >= - r.
Proof. now intros r I; rewrite <-Ropp_0; apply Ropp_le_ge_contravar. Qed.
#[global]
Hint Resolve Ropp_0_le_ge_contravar: real.

Lemma Ropp_0_ge_le_contravar : forall r, 0 >= r -> 0 <= - r.
Proof. now intros r I; rewrite <-Ropp_0; apply Ropp_ge_le_contravar. Qed.
#[global]
Hint Resolve Ropp_0_ge_le_contravar: real.

(** *** Cancellation *)

Lemma Ropp_lt_cancel : forall r1 r2, - r2 < - r1 -> r1 < r2.
Proof. now intros r1 r2 I%Ropp_lt_contravar; rewrite 2Ropp_involutive in I. Qed.
#[global]
Hint Immediate Ropp_lt_cancel: real.

Lemma Ropp_gt_cancel : forall r1 r2, - r2 > - r1 -> r1 > r2.
Proof. now intros r1 r2; apply Ropp_lt_cancel. Qed.

Lemma Ropp_le_cancel : forall r1 r2, - r2 <= - r1 -> r1 <= r2.
Proof. now intros r1 r2 I%Ropp_le_contravar; rewrite 2Ropp_involutive in I. Qed.
#[global]
Hint Immediate Ropp_le_cancel: real.

Lemma Ropp_ge_cancel : forall r1 r2, - r2 >= - r1 -> r1 >= r2.
Proof. now intros r1 r2 I%Rge_le; apply Rle_ge, Ropp_le_cancel. Qed.

(** *** Sign of opposite *)

Lemma Ropp_pos : forall r, r > 0 -> - r < 0.
Proof. now intros r H; rewrite <-Ropp_0; apply Ropp_lt_contravar. Qed.

Lemma Ropp_neg : forall r, r < 0 -> - r > 0.
Proof. now intros r H; rewrite <-Ropp_0; apply Ropp_lt_contravar. Qed.

(*********************************************************)
(** ** Order and multiplication                          *)
(*********************************************************)

(** Remark: [Rmult_lt_compat_l] is in [Raxioms.v] *)

(** *** Covariant compatibility *)

Lemma Rmult_lt_compat_r : forall r r1 r2, 0 < r -> r1 < r2 -> r1 * r < r2 * r.
Proof.
  intros r r1 r2; rewrite 2(Rmult_comm _ r); apply Rmult_lt_compat_l.
Qed.
#[global]
(* TODO: why core? *)
Hint Resolve Rmult_lt_compat_r : core.

Lemma Rmult_gt_compat_r : forall r r1 r2, r > 0 -> r1 > r2 -> r1 * r > r2 * r.
Proof. now intros r r1 r2; apply Rmult_lt_compat_r. Qed.

Lemma Rmult_gt_compat_l : forall r r1 r2, r > 0 -> r1 > r2 -> r * r1 > r * r2.
Proof. now intros r r1 r2; apply Rmult_lt_compat_l. Qed.

Lemma Rmult_le_compat_l :
  forall r r1 r2, 0 <= r -> r1 <= r2 -> r * r1 <= r * r2.
Proof.
  intros r r1 r2 [I | <-] [I' | ->]; try rewrite 2Rmult_0_l; try apply Rle_refl.
  now left; apply Rmult_lt_compat_l.
Qed.
#[global]
Hint Resolve Rmult_le_compat_l: real.

Lemma Rmult_le_compat_r :
  forall r r1 r2, 0 <= r -> r1 <= r2 -> r1 * r <= r2 * r.
Proof.
  now intros r r1 r2 H; rewrite 2(Rmult_comm _ r); apply Rmult_le_compat_l.
Qed.
#[global]
Hint Resolve Rmult_le_compat_r: real.

Lemma Rmult_ge_compat_l :
  forall r r1 r2, r >= 0 -> r1 >= r2 -> r * r1 >= r * r2.
Proof.
  now intros r r1 r2 I%Rge_le J%Rge_le; apply Rle_ge, Rmult_le_compat_l.
Qed.

Lemma Rmult_ge_compat_r :
  forall r r1 r2, r >= 0 -> r1 >= r2 -> r1 * r >= r2 * r.
Proof.
  now intros r r1 r2; rewrite 2(Rmult_comm _ r); apply Rmult_ge_compat_l.
Qed.

Lemma Rmult_le_compat :
  forall r1 r2 r3 r4,
    0 <= r1 -> 0 <= r3 -> r1 <= r2 -> r3 <= r4 -> r1 * r3 <= r2 * r4.
Proof.
  intros r1 r2 r3 r4 H1 H2 I J; apply (Rle_trans _ (r2 * r3)).
  - now apply Rmult_le_compat_r.
  - assert (H3 : 0 <= r2) by now apply (Rle_trans _ r1).
    now apply Rmult_le_compat_l.
Qed.
#[global]
Hint Resolve Rmult_le_compat: real.

Lemma Rmult_le_pos : forall r1 r2, 0 <= r1 -> 0 <= r2 -> 0 <= r1 * r2.
Proof.
  now intros r1 r2 I I'; rewrite <-(Rmult_0_l 0); apply Rmult_le_compat;
    try apply Rle_refl.
Qed.

Lemma Rmult_ge_compat :
  forall r1 r2 r3 r4,
    r2 >= 0 -> r4 >= 0 -> r1 >= r2 -> r3 >= r4 -> r1 * r3 >= r2 * r4.
Proof.
  intros r1 r2 r3 r4 H1%Rge_le H2%Rge_le I%Rge_le J%Rge_le; apply Rle_ge.
  now apply Rmult_le_compat.
Qed.

Lemma Rmult_ge_0_gt_0_lt_compat :
  forall r1 r2 r3 r4,
    r3 >= 0 -> r2 > 0 -> r1 < r2 -> r3 < r4 -> r1 * r3 < r2 * r4.
Proof.
  intros r1 r2 r3 r4 H1%Rge_le H2 I J; apply (Rle_lt_trans _ (r2 * r3)).
  - now apply Rmult_le_compat_r; try apply (Rlt_le r1).
  - now apply Rmult_lt_compat_l.
Qed.

Lemma Rmult_gt_0_lt_compat :
  forall r1 r2 r3 r4,
    r3 > 0 -> r2 > 0 -> r1 < r2 -> r3 < r4 -> r1 * r3 < r2 * r4.
Proof. now intros r1 r2 r3 r4 H1%Rgt_ge; apply Rmult_ge_0_gt_0_lt_compat. Qed.

Lemma Rmult_le_0_lt_compat :
  forall r1 r2 r3 r4,
    0 <= r1 -> 0 <= r3 -> r1 < r2 -> r3 < r4 -> r1 * r3 < r2 * r4.
Proof.
  intros r1 r2 r3 r4 H1 H2 I J; apply Rle_lt_trans with (r2 * r3).
  - now apply Rlt_le in I; apply Rmult_le_compat_r.
  - assert (H3 : 0 < r2) by now apply (Rle_lt_trans _ r1).
    now apply Rmult_lt_compat_l.
Qed.

(** *** Contravariant compatibility *)

Lemma Rmult_le_compat_neg_l :
  forall r r1 r2, r <= 0 -> r1 <= r2 -> r * r2 <= r * r1.
Proof.
  intros r r1 r2 I%Ropp_le_contravar J; rewrite Ropp_0 in I.
  now apply Ropp_le_cancel; rewrite 2Ropp_mult_distr_l; apply Rmult_le_compat_l.
Qed.
#[global]
Hint Resolve Rmult_le_compat_neg_l: real.

Lemma Rmult_le_ge_compat_neg_l :
  forall r r1 r2, r <= 0 -> r1 <= r2 -> r * r1 >= r * r2.
Proof. now intros r r1 r2 H I; apply Rle_ge, Rmult_le_compat_neg_l. Qed.
#[global]
Hint Resolve Rmult_le_ge_compat_neg_l: real.

Lemma Rmult_lt_gt_compat_neg_l :
  forall r r1 r2, r < 0 -> r1 < r2 -> r * r1 > r * r2.
Proof.
  intros r r1 r2 I%Ropp_lt_contravar J; rewrite Ropp_0 in I.
  now apply Ropp_lt_cancel; rewrite 2Ropp_mult_distr_l; apply Rmult_lt_compat_l.
Qed.

(** *** Sign of multiplication *)

Lemma Rmult_lt_0_compat : forall r1 r2, 0 < r1 -> 0 < r2 -> 0 < r1 * r2.
Proof.
  now intros r1 r2 I J; rewrite <-(Rmult_0_l 0); apply Rmult_le_0_lt_compat;
    try apply Rle_refl.
Qed.

Lemma Rmult_gt_0_compat : forall r1 r2, r1 > 0 -> r2 > 0 -> r1 * r2 > 0.
Proof. exact Rmult_lt_0_compat. Qed.

Definition Rmult_pos_pos := Rmult_gt_0_compat.

Lemma Rmult_neg_neg : forall r1 r2, r1 < 0 -> r2 < 0 -> r1 * r2 > 0.
Proof.
  intros r1 r2 H1%Ropp_lt_contravar H2%Ropp_lt_contravar.
  rewrite Ropp_0 in H1, H2; rewrite <-Rmult_opp_opp.
  now apply Rmult_lt_0_compat.
Qed.

Lemma Rmult_neg_pos : forall r1 r2, r1 < 0 -> r2 > 0 -> r1 * r2 < 0.
Proof.
  intros r1 r2 H1 H2.
  now rewrite <-(Rmult_0_r r1); apply Rmult_lt_gt_compat_neg_l.
Qed.

Lemma Rmult_pos_neg : forall r1 r2, r1 > 0 -> r2 < 0 -> r1 * r2 < 0.
Proof. now intros r1 r2 H1 H2; rewrite Rmult_comm; apply Rmult_neg_pos. Qed.

Lemma Rmult_pos_cases :
  forall r1 r2, r1 * r2 > 0 -> (r1 > 0 /\ r2 > 0) \/ (r1 < 0 /\ r2 < 0).
Proof.
  intros r1 r2.
  destruct (Rtotal_order r1 0) as [Hlt1 | [-> | Hgt1]]; cycle 1.
  - now intros H; exfalso; rewrite Rmult_0_l in H; apply (Rlt_irrefl 0).
  - destruct (Rtotal_order r2 0) as [Hlt2 | [-> | Hgt2]]; cycle 1.
    + now intros H; exfalso; rewrite Rmult_0_r in H; apply (Rlt_irrefl 0).
    + now intros _; left.
    + intros H; exfalso; apply (Rgt_not_le (r1 * r2) 0); try easy.
      now left; apply Rmult_pos_neg.
  - destruct (Rtotal_order r2 0) as [Hlt2 | [-> | Hgt2]]; cycle 1.
    + now intros H; exfalso; rewrite Rmult_0_r in H; apply (Rlt_irrefl 0).
    + intros H; exfalso; apply (Rgt_not_le (r1 * r2) 0); try easy.
      now left; apply Rmult_neg_pos.
    + now intros _; right.
Qed.

Lemma Rmult_neg_cases :
  forall r1 r2, r1 * r2 < 0 -> (r1 > 0 /\ r2 < 0) \/ (r1 < 0 /\ r2 > 0).
Proof.
  intros r1 r2 H%Ropp_lt_contravar%Rlt_gt.
  rewrite Ropp_0, Ropp_mult_distr_l in H.
  apply Rmult_pos_cases in H as
    [[H1%Ropp_lt_contravar H2] | [H1%Ropp_lt_contravar H2]].
  - now right; split; [| assumption]; rewrite Ropp_involutive, Ropp_0 in H1.
  - now left; split; [| assumption]; rewrite Ropp_involutive, Ropp_0 in H1.
Qed.

(** *** Order and square function *)

Lemma Rle_0_sqr : forall r, 0 <= Rsqr r.
Proof.
  unfold Rsqr; intros r.
  destruct (Rlt_le_dec r 0) as [Hneg%Ropp_lt_contravar%Rlt_le | Hge0].
  - rewrite Ropp_0 in Hneg; rewrite <-Rmult_opp_opp, <-(Rmult_0_l 0).
    now apply Rmult_le_compat; try apply Rle_refl.
  - now rewrite <-(Rmult_0_l 0); apply Rmult_le_compat; try apply Rle_refl.
Qed.

Lemma Rlt_0_sqr : forall r, r <> 0 -> 0 < Rsqr r.
Proof.
  now intros r Hr; destruct (Rle_0_sqr r) as [Hle | Eq%eq_sym%Rsqr_0_uniq].
Qed.
#[global]
Hint Resolve Rle_0_sqr Rlt_0_sqr: real.

Lemma Rplus_sqr_eq_0 :
  forall r1 r2, Rsqr r1 + Rsqr r2 = 0 -> r1 = 0 /\ r2 = 0.
Proof.
  assert (E : forall r1 r2, Rsqr r1 + Rsqr r2 = 0 -> r1 = 0). {
    intros r1 r2 H; apply Rsqr_0_uniq, Rplus_eq_0_l with (3 := H);
    now apply Rle_0_sqr.
  }
  intros r1 r2 H; split.
  - now apply (E _ r2).
  - now rewrite Rplus_comm in H; apply (E _ r1).
Qed.

(** *** Zero is less than one *)

Lemma Rlt_0_1 : 0 < 1.
Proof. now rewrite <-(Rmult_1_r 1), <-Rsqr_def; apply Rlt_0_sqr, R1_neq_R0. Qed.
#[global]
Hint Resolve Rlt_0_1: real.

Lemma Rle_0_1 : 0 <= 1.
Proof. left; exact Rlt_0_1. Qed.

(** *** Sign of inverse *)

Lemma Rinv_0_lt_compat : forall r, 0 < r -> 0 < / r.
Proof.
  intros r Hr.
  destruct (Rlt_or_le 0 (/ r)) as [Hlt | Hle]; try easy.
  exfalso; apply (Rle_not_lt 0 1); try apply Rlt_0_1.
  rewrite <-(Rinv_l r), <-(Rmult_0_r (/ r)); cycle 1.
  { now apply not_eq_sym, Rlt_not_eq. }
  now apply Rlt_le in Hr; apply Rmult_le_compat_neg_l.
Qed.
#[global]
Hint Resolve Rinv_0_lt_compat: real.

Lemma Rinv_lt_0_compat : forall r, r < 0 -> / r < 0.
Proof.
  intros r H%Ropp_lt_contravar; apply Ropp_lt_cancel.
  now rewrite Ropp_0 in H |- *; rewrite <-Rinv_opp; apply Rinv_0_lt_compat.
Qed.
#[global]
Hint Resolve Rinv_lt_0_compat: real.

(** *** Cancellation in inequalities of products *)

Lemma Rmult_lt_reg_l : forall r r1 r2, 0 < r -> r * r1 < r * r2 -> r1 < r2.
Proof.
  intros r r1 r2 Hr I%(Rmult_lt_compat_l (/ r)); try now apply Rinv_0_lt_compat.
  rewrite <-2(Rmult_assoc (/ r)), Rinv_l, 2Rmult_1_l in I; try easy.
    now apply not_eq_sym, Rlt_not_eq.
Qed.

Lemma Rmult_lt_reg_r : forall r r1 r2 : R, 0 < r -> r1 * r < r2 * r -> r1 < r2.
Proof.
  intros r r1 r2 H I; apply (Rmult_lt_reg_l r); try easy.
  now rewrite 2(Rmult_comm r).
Qed.

Lemma Rmult_gt_reg_l : forall r r1 r2, 0 < r -> r * r1 < r * r2 -> r1 < r2.
Proof. now intros r r1 r2; apply Rmult_lt_reg_l. Qed.

Lemma Rmult_gt_reg_r : forall r r1 r2, r > 0 -> r1 * r > r2 * r -> r1 > r2.
Proof. now intros r r1 r2; apply Rmult_lt_reg_r. Qed.

Lemma Rmult_le_reg_l : forall r r1 r2, 0 < r -> r * r1 <= r * r2 -> r1 <= r2.
Proof.
  intros r r1 r2 Hr [I | E].
  - now left; apply (Rmult_lt_reg_l r).
  - now apply Rlt_not_eq, not_eq_sym in Hr; right; apply (Rmult_eq_reg_l r).
Qed.

Lemma Rmult_le_reg_r : forall r r1 r2, 0 < r -> r1 * r <= r2 * r -> r1 <= r2.
Proof.
  intros r r1 r2 Hr I; rewrite 2(Rmult_comm _ r) in I.
  now apply (Rmult_le_reg_l r).
Qed.

(** *** Order and inverse *)

Lemma Rinv_0_lt_contravar : forall r1 r2, 0 < r1 -> r1 < r2 -> / r2 < / r1.
Proof.
  intros r1 r2 H1 I.
  assert (H2 : 0 < r2) by now apply (Rlt_trans _ r1).
  apply (Rmult_lt_reg_l r2); try easy.
  rewrite Rinv_r by now apply Rgt_not_eq.
  apply (Rmult_lt_reg_r r1); try easy.
  rewrite Rmult_assoc, Rinv_l by now apply Rgt_not_eq.
  now rewrite Rmult_1_r, Rmult_1_l.
Qed.
#[global]
Hint Resolve Rinv_0_lt_contravar: real.

Lemma Rinv_lt_0_contravar : forall r1 r2, r2 < 0 -> r1 < r2 -> / r2 < / r1.
Proof.
  intros r1 r2 H2%Ropp_lt_contravar I%Ropp_lt_contravar.
  apply Ropp_lt_cancel.
  rewrite Ropp_0 in H2.
  now rewrite <-2(Rinv_opp); apply Rinv_0_lt_contravar.
Qed.
#[global]
Hint Resolve Rinv_lt_0_contravar: real.

(* TODO: We may want to deprecate it but cannot because of the hint used in
   external libs (the stdlib can already be compiled without it) *)
Lemma Rinv_1_lt_contravar : forall r1 r2, 1 <= r1 -> r1 < r2 -> / r2 < / r1.
Proof.
  intros r1 r2 H1 I.
  apply Rlt_le_trans with (1 := Rlt_0_1) in H1.
  now apply Rinv_0_lt_contravar.
Qed.
#[global]
Hint Resolve Rinv_1_lt_contravar: real.

Lemma Rinv_lt_contravar : forall r1 r2, 0 < r1 * r2 -> r1 < r2 -> / r2 < / r1.
Proof.
  intros r1 r2 [[H1 H2] | [H1 H2]]%Rmult_pos_cases.
  - now apply Rinv_0_lt_contravar.
  - now apply Rinv_lt_0_contravar.
Qed.

(* NOTE: keeping inconsistent variable names for backward compatibility. *)
Lemma Rinv_le_contravar :
  forall x y, 0 < x -> x <= y -> / y <= / x.
Proof.
  intros r1 r2 H1 [H2 | ->].
  - now apply Rlt_le, Rinv_0_lt_contravar.
  - now apply Rle_refl.
Qed.

(** *** Sign of inverse *)

Lemma Rinv_pos : forall r, r > 0 -> / r > 0.
Proof. now intros r; apply Rinv_0_lt_compat. Qed.

Lemma Rinv_neg : forall r, r < 0 -> / r < 0.
Proof. now intros r; apply Rinv_lt_0_compat. Qed.

(*********************************************************)
(** ** Order and subtraction                            *)
(*********************************************************)

Lemma Rlt_minus : forall r1 r2, r1 < r2 -> r1 - r2 < 0.
Proof.
  unfold Rminus; intros r1 r2 H%(Rplus_lt_compat_r (-r2)).
  now rewrite Rplus_opp_r in H.
Qed.
#[global]
Hint Resolve Rlt_minus: real.

Lemma Rgt_minus : forall r1 r2, r1 > r2 -> r1 - r2 > 0.
Proof.
  unfold Rminus; intros r1 r2 H%(Rplus_lt_compat_r (-r2)).
  now rewrite Rplus_opp_r in H.
Qed.

Lemma Rle_minus : forall r1 r2, r1 <= r2 -> r1 - r2 <= 0.
Proof.
  unfold Rminus; intros r1 r2 H%(Rplus_le_compat_r (-r2)).
  now rewrite Rplus_opp_r in H.
Qed.

Lemma Rge_minus : forall r1 r2, r1 >= r2 -> r1 - r2 >= 0.
Proof.
  unfold Rminus; intros r1 r2 H%(Rplus_ge_compat_r (-r2)).
  now rewrite Rplus_opp_r in H.
Qed.

Lemma Rminus_lt : forall r1 r2, r1 - r2 < 0 -> r1 < r2.
Proof.
  unfold Rminus; intros r1 r2 H.
  now apply (Rplus_lt_reg_r (-r2)); rewrite Rplus_opp_r.
Qed.

Lemma Rminus_gt : forall r1 r2, r1 - r2 > 0 -> r1 > r2.
Proof.
  unfold Rminus; intros r1 r2 H.
  now apply (Rplus_lt_reg_r (-r2)); rewrite Rplus_opp_r.
Qed.

Lemma Rlt_minus_0 : forall r1 r2, r1 - r2 < 0 <-> r1 < r2.
Proof.
  intros r1 r2; split.
  - now apply Rminus_lt.
  - now apply Rlt_minus.
Qed.

Lemma Rlt_0_minus : forall r1 r2, 0 < r2 - r1 <-> r1 < r2.
Proof.
  intros r1 r2; split.
  - now apply Rminus_gt.
  - now apply Rgt_minus.
Qed.

Lemma Rminus_le : forall r1 r2, r1 - r2 <= 0 -> r1 <= r2.
Proof.
  unfold Rminus; intros r1 r2 H.
  now apply (Rplus_le_reg_r (-r2)); rewrite Rplus_opp_r.
Qed.

Lemma Rminus_ge : forall r1 r2, r1 - r2 >= 0 -> r1 >= r2.
Proof.
  unfold Rminus; intros r1 r2 H.
  now apply (Rplus_ge_reg_r (-r2)); rewrite Rplus_opp_r.
Qed.

Lemma Rgt_minus_pos : forall r1 r2, 0 < r2 -> r1 > r1 - r2.
Proof.
  intros r1 r2 H%Ropp_lt_contravar; rewrite Ropp_0 in H.
  now rewrite <-(Rplus_0_r r1) at 1; apply (Rplus_lt_compat_l r1).
Qed.

(*********************************************************)
(** ** Division                                          *)
(*********************************************************)

Lemma Rdiv_def : forall r1 r2, r1 / r2 = r1 * / r2.
Proof. now unfold Rdiv. Qed.

Lemma Rdiv_eq_compat_l : forall r r1 r2, r1 = r2 -> r / r1 = r / r2.
Proof.
  now unfold Rdiv; intros r r1 r2 H%Rinv_eq_compat; apply Rmult_eq_compat_l.
Qed.

Lemma Rdiv_eq_compat_r : forall r r1 r2, r1 = r2 -> r1 / r = r2 / r.
Proof. now unfold Rdiv; intros r r1 r2; apply Rmult_eq_compat_r. Qed.

Lemma Rdiv_eq_reg_l : forall r r1 r2, r / r1 = r / r2 -> r <> 0 -> r1 = r2.
Proof.
  now unfold Rdiv; intros r r1 r2 H H'; apply Rinv_eq_reg, (Rmult_eq_reg_l r).
Qed.

Lemma Rdiv_eq_reg_r : forall r r1 r2, r1 / r = r2 / r -> r <> 0 -> r1 = r2.
Proof.
  now unfold Rdiv; intros r r1 r2 H H'%Rinv_neq_0_compat;
    apply (Rmult_eq_reg_r (/ r)).
Qed.

Lemma Rdiv_0_l : forall r, 0 / r = 0.
Proof. now unfold Rdiv; intros r; rewrite Rmult_0_l. Qed.

Lemma Rdiv_0_r : forall r, r / 0 = 0.
Proof. now unfold Rdiv; intros r; rewrite Rinv_0, Rmult_0_r. Qed.

Lemma Rdiv_1_l : forall r, 1 / r = / r.
Proof. now unfold Rdiv; intros r; rewrite Rmult_1_l. Qed.

Lemma Rdiv_1_r : forall r, r / 1 = r.
Proof. now unfold Rdiv; intros r; rewrite Rinv_1, Rmult_1_r. Qed.

Lemma Rdiv_diag : forall r, r <> 0 -> r / r = 1.
Proof. now unfold Rdiv; intros r H; rewrite Rinv_r. Qed.

Lemma Rdiv_diag_eq : forall r1 r2, r2 <> 0 -> r1 = r2 -> r1 / r2 = 1.
Proof. now intros r1 r2 H <-; apply Rdiv_diag. Qed.

Lemma Rmult_div_l : forall r1 r2, r2 <> 0 -> r1 * r2 / r2 = r1.
Proof.
  now unfold Rdiv; intros r1 r2 H; rewrite Rmult_assoc, Rinv_r, Rmult_1_r.
Qed.

Lemma Rmult_div_r : forall r1 r2, r1 <> 0 -> r1 * r2 / r1 = r2.
Proof. now intros r1 r2 H; rewrite Rmult_comm, Rmult_div_l. Qed.

Lemma Rmult_div_assoc : forall r1 r2 r3, r1 * (r2 / r3) = r1 * r2 / r3.
Proof. now unfold Rdiv; intros r1 r2 r3; rewrite Rmult_assoc. Qed.

Lemma Rmult_div_swap : forall r1 r2 r3, r1 * r2 / r3 = r1 / r3 * r2.
Proof.
  unfold Rdiv; intros r1 r2 r3.
  now rewrite Rmult_assoc, (Rmult_comm r2), <-Rmult_assoc.
Qed.

Lemma Rdiv_diag_uniq : forall r1 r2, r1 / r2 = 1 -> r1 = r2.
Proof.
  intros r1 r2; destruct (Req_dec r2 0) as [-> | Hn0].
  - now intros H; rewrite Rdiv_0_r in H; exfalso; apply R1_neq_R0; symmetry.
  - intros H%(Rmult_eq_compat_r r2).
    now rewrite <-Rmult_div_swap, Rmult_div_l, Rmult_1_l in H.
Qed.

Lemma Rdiv_mult_distr : forall r1 r2 r3, r1 / (r2 * r3) = r1 / r2 / r3.
Proof. now unfold Rdiv; intros r1 r2 r3; rewrite Rinv_mult, Rmult_assoc. Qed.

Lemma Rdiv_mult_r_r :
  forall r r1 r2, r <> 0 -> (r1 * r) / (r2 * r) = r1 / r2.
Proof.
  intros r r1 r2 H.
  rewrite <-Rmult_div_assoc, (Rmult_comm r2), Rdiv_mult_distr.
  now rewrite Rdiv_diag by exact H; rewrite Rdiv_1_l, Rdiv_def.
Qed.

Lemma Rdiv_mult_l_r :
  forall r r1 r2, r <> 0 -> (r * r1) / (r2 * r) = r1 / r2.
Proof.
  now intros r r1 r2; rewrite (Rmult_comm r); apply Rdiv_mult_r_r.
Qed.

Lemma Rdiv_mult_l_l :
  forall r r1 r2, r <> 0 -> (r * r1) / (r * r2) = r1 / r2.
Proof.
  now intros r r1 r2; rewrite (Rmult_comm _ r2); apply Rdiv_mult_l_r.
Qed.

Lemma Rdiv_mult_r_l :
  forall r r1 r2, r <> 0 -> (r1 * r) / (r * r2) = r1 / r2.
Proof.
  now intros r r1 r2; rewrite (Rmult_comm r1); apply Rdiv_mult_l_l.
Qed.

Lemma Ropp_div_distr_l : forall r1 r2, - (r1 / r2) = - r1 / r2.
Proof. unfold Rdiv; intros r1 r2; now apply Ropp_mult_distr_l. Qed.

Lemma Ropp_div_distr_r : forall r1 r2, r1 / - r2 = - (r1 / r2).
Proof. now unfold Rdiv; intros r1 r2; rewrite Ropp_mult_distr_r, Rinv_opp. Qed.

(* NOTE: keeping inconsistent variable names for backward compatibility. *)
Lemma Rdiv_plus_distr : forall a b c, (a + b) / c = a / c + b / c.
Proof. intros r1 r2 r; now apply Rmult_plus_distr_r. Qed.

(* NOTE: keeping inconsistent variable names for backward compatibility. *)
Lemma Rdiv_minus_distr : forall a b c, (a - b) / c = a / c - b / c.
Proof.
  unfold Rminus; intros r1 r2 r.
  now rewrite Ropp_div_distr_l; apply Rdiv_plus_distr.
Qed.

(* NOTE: keeping inconsistent variable names for backward compatibility. *)
Lemma Rinv_div x y : / (x / y) = y / x.
Proof. now unfold Rdiv; rewrite Rinv_mult, Rinv_inv; apply Rmult_comm. Qed.

(* NOTE: keeping inconsistent variable names for backward compatibility. *)
Lemma Rdiv_lt_0_compat : forall a b, 0 < a -> 0 < b -> 0 < a / b.
Proof.
  intros r1 r2 r1_pos r2_pos.
  now apply (Rmult_lt_0_compat r1 (/ r2) r1_pos), Rinv_0_lt_compat.
Qed.

Lemma Rdiv_opp_l : forall r1 r2, - r1 / r2 = - (r1 / r2).
Proof. now intros r1 r2; rewrite Ropp_div_distr_l. Qed.

(* NOTE: keeping inconsistent variable names for backward compatibility. *)
Lemma Rdiv_opp_r : forall x y, x / - y = - (x / y).
Proof. now intros r1 r2; rewrite Ropp_div_distr_r. Qed.

(** *** Sign of division *)

Lemma Rdiv_pos_pos : forall r1 r2, r1 > 0 -> r2 > 0 -> r1 / r2 > 0.
Proof. now unfold Rdiv; intros r1 r2 H H'%Rinv_pos; apply Rmult_pos_pos. Qed.

Lemma Rdiv_pos_neg : forall r1 r2, r1 > 0 -> r2 < 0 -> r1 / r2 < 0.
Proof. now unfold Rdiv; intros r1 r2 H H'%Rinv_neg; apply Rmult_pos_neg. Qed.

Lemma Rdiv_neg_pos : forall r1 r2, r1 < 0 -> r2 > 0 -> r1 / r2 < 0.
Proof. now unfold Rdiv; intros r1 r2 H H'%Rinv_pos; apply Rmult_neg_pos. Qed.

Lemma Rdiv_neg_neg : forall r1 r2, r1 < 0 -> r2 < 0 -> r1 / r2 > 0.
Proof. now unfold Rdiv; intros r1 r2 H H'%Rinv_neg; apply Rmult_neg_neg. Qed.

Lemma Rdiv_pos_cases :
  forall r1 r2 : R, r1 / r2 > 0 -> r1 > 0 /\ r2 > 0 \/ r1 < 0 /\ r2 < 0.
Proof.
  unfold Rdiv; intros r1 r2 [[I J%Rinv_pos] | [I J%Rinv_neg]]%Rmult_pos_cases.
  - now left; rewrite Rinv_inv in J.
  - now right; rewrite Rinv_inv in J.
Qed.

(*********************************************************)
(** ** Miscellaneous                                     *)
(*********************************************************)

(* This can't be moved to "Order and addition" because of Rlt_0_1 which
   is proved using a sign rule. *)

(* TODO: We may want to deprecate it but cannot because of the hint used in
   external libs (the stdlib can already be compiled without it) *)
Lemma Rle_lt_0_plus_1 : forall r, 0 <= r -> 0 < r + 1.
Proof.
  intros r H; apply Rlt_le_trans with (1 := Rlt_0_1).
  rewrite <-(Rplus_0_l 1) at 1.
  apply Rplus_le_compat; try easy.
Qed.
#[global]
Hint Resolve Rle_lt_0_plus_1: real.

(* TODO: We may want to deprecate it but cannot because of the hint used in
   external libs (the stdlib can already be compiled without it) *)
Lemma Rlt_plus_1 : forall r, r < r + 1.
Proof.
  intros r; rewrite <-(Rplus_0_r r) at 1; apply Rplus_le_lt_compat.
  - now apply Rle_refl.
  - exact Rlt_0_1.
Qed.
#[global]
Hint Resolve Rlt_plus_1: real.

Lemma Rlt_0_2 : 0 < 2.
Proof.
  assert (H : 0 < 1) by exact Rlt_0_1.
  apply (Rlt_trans _ 1); try easy.
  replace 2 with (1 + 1) by reflexivity.
  rewrite <-(Rplus_0_l 1) at 1.
  apply Rplus_lt_le_compat; try easy.
Qed.

Lemma Rplus_diag : forall r, r + r = 2 * r.
Proof.
  intros r; replace 2 with (1 + 1) by reflexivity.
  now rewrite Rmult_plus_distr_r, Rmult_1_l.
Qed.

Lemma Rplus_half_diag : forall r, r / 2 + r / 2 = r.
Proof.
  intros r; rewrite <-Rdiv_plus_distr, Rplus_diag, Rmult_div_r; [easy |].
  now apply not_eq_sym, Rlt_not_eq, Rlt_0_2.
Qed.

Lemma Rlt_half_plus : forall r1 r2, r1 < r2 -> r1 < (r1 + r2) / 2 < r2.
Proof.
  pose proof Rlt_0_2 as two_gt_0.
  assert (E : forall r r', (r + r') / 2 * 2 = r + r'). {
    now intros r r'; rewrite Rdiv_plus_distr, Rmult_plus_distr_r,
      <-2Rmult_div_swap, 2Rmult_div_l by (now apply Rgt_not_eq).
  }
  intros r1 r2 r1_lt_r2; split; apply Rmult_lt_reg_r with (1 := two_gt_0);
    rewrite E, Rmult_comm, <-Rplus_diag.
  - now apply Rplus_lt_compat_l.
  - now apply Rplus_lt_compat_r.
Qed.

Lemma Rle_half_plus : forall r1 r2, r1 <= r2 -> r1 <= (r1 + r2) / 2 <= r2.
Proof.
  intros r1 r2 [I | ->].
  - now split; left; apply (Rlt_half_plus r1 r2).
  - now split; rewrite Rdiv_plus_distr, Rplus_half_diag; apply Rle_refl.
Qed.

Lemma Rexists_between : forall r1 r2, r1 < r2 -> exists r, r1 < r < r2.
Proof.
  intros r1 r2 r1_lt_r2.
  exists ((r1 + r2) / 2).
  now apply Rlt_half_plus.
Qed.

Lemma Rle_plus_epsilon :
  forall r1 r2, (forall eps:R, 0 < eps -> r1 <= r2 + eps) -> r1 <= r2.
Proof.
  intros r1 r2 H.
  destruct (Rle_or_lt r1 r2) as [r1_le_r2 | r1_gt_r2]; [assumption |].
  exfalso.
  destruct (Rexists_between r2 r1) as [r [r2_lt_r r_lt_r1]]; [assumption |].
  apply (Rlt_irrefl r1), (Rle_lt_trans _ r); [| assumption].
  rewrite <-(Rplus_minus r2 r).
  now apply H, Rgt_minus.
Qed.

(** Remark : a sigma-type version, called [completeness] is in [Raxioms.v] *)
Lemma upper_bound_thm :
  forall E : R -> Prop,
    bound E -> (exists x : R, E x) ->  exists m : R, is_lub E m.
Proof.
  intros E E_bnd E_inhab.
  destruct (completeness E E_bnd E_inhab) as [x xlub].
  now exists x.
Qed.

(*********************************************************)
(** ** Injection from [nat] to [R]                       *)
(*********************************************************)

Lemma S_INR : forall n, INR (S n) = INR n + 1.
Proof.
  intros [| n'].
  - now cbv -[IZR]; rewrite Rplus_0_l.
  - reflexivity.
Qed.

Lemma INR_0 : INR 0 = 0.
Proof. reflexivity. Qed.

Lemma INR_1 : INR 1 = 1.
Proof. reflexivity. Qed.

Lemma plus_INR : forall n m, INR (n + m) = INR n + INR m.
Proof.
  intros n m; induction m as [| m IHm].
  - now rewrite Nat.add_0_r, INR_0, Rplus_0_r.
  - now rewrite Nat.add_succ_r, 2S_INR, IHm, Rplus_assoc.
Qed.
#[global]
Hint Resolve plus_INR: real.

Lemma minus_INR : forall n m, (m <= n)%nat -> INR (n - m) = INR n - INR m.
Proof.
  intros n m le; induction le as [|n' H' IH].
  - now rewrite Nat.sub_diag, Rminus_diag.
  - rewrite Nat.sub_succ_l by assumption.
    now rewrite 2S_INR, IH, Rplus_minus_swap.
Qed.
#[global]
Hint Resolve minus_INR: real.

Lemma mult_INR : forall n m:nat, INR (n * m) = INR n * INR m.
Proof.
  intros n m; induction m as [| m IH].
  - now rewrite Nat.mul_0_r, INR_0, Rmult_0_r.
  - now rewrite Nat.mul_succ_r, S_INR, plus_INR, IH,
      Rmult_plus_distr_l, Rmult_1_r.
Qed.
#[global]
Hint Resolve mult_INR: real.

Lemma pow_INR : forall m n:nat, INR (m ^ n) = pow (INR m) n.
Proof.
  now intros m n; induction n as [| n IH]; [| simpl; rewrite mult_INR, IH].
Qed.

Lemma lt_0_INR : forall n:nat, (0 < n)%nat -> 0 < INR n.
Proof.
  induction n as [| [|n ] IHn]; intros H.
  - now inversion H.
  - now rewrite INR_1; apply Rlt_0_1.
  - rewrite S_INR; apply Rplus_lt_0_compat.
    + now apply IHn, Nat.lt_0_succ.
    + exact Rlt_0_1.
Qed.
#[global]
Hint Resolve lt_0_INR: real.

Lemma lt_INR : forall n m:nat, (n < m)%nat -> INR n < INR m.
Proof.
  induction n as [| n IH]; intros m H.
  - now apply lt_0_INR.
  - destruct m as [| m'].
    + now apply Nat.nlt_0_r in H.
    + rewrite 2S_INR.
      now apply (Rplus_lt_compat_r 1), IH, Nat.succ_lt_mono.
Qed.
#[global]
Hint Resolve lt_INR: real.

Lemma lt_1_INR : forall n:nat, (1 < n)%nat -> 1 < INR n.
Proof. now apply lt_INR. Qed.
#[global]
Hint Resolve lt_1_INR: real.

Lemma pos_INR_nat_of_P : forall p:positive, 0 < INR (Pos.to_nat p).
Proof. now intros p; apply lt_0_INR, Pos2Nat.is_pos. Qed.
#[global]
Hint Resolve pos_INR_nat_of_P: real.

Lemma pos_INR : forall n:nat, 0 <= INR n.
Proof.
  intros [| n].
  - now rewrite INR_0; apply Rle_refl.
  - now left; apply lt_0_INR, Nat.lt_0_succ.
Qed.
#[global]
Hint Resolve pos_INR: real.

Lemma INR_lt : forall n m:nat, INR n < INR m -> (n < m)%nat.
Proof.
  intros n m. generalize dependent n.
  induction m as [| m IH]; intros n H.
  - now exfalso; apply Rlt_not_le with (1 := H), pos_INR.
  - destruct n as [| n].
    + apply Nat.lt_0_succ.
    + apply ->Nat.succ_lt_mono; apply IH.
      rewrite 2!S_INR in H.
      now apply Rplus_lt_reg_r with (1 := H).
Qed.
#[global]
Hint Resolve INR_lt: real.

Lemma le_INR : forall n m:nat, (n <= m)%nat -> INR n <= INR m.
Proof.
  intros n m [I | ->]%Nat.le_lteq.
  - now left; apply lt_INR.
  - now right.
Qed.
#[global]
Hint Resolve le_INR: real.

Lemma INR_not_0 : forall n:nat, INR n <> 0 -> n <> 0%nat.
Proof. now intros n H ->; apply H, INR_0. Qed.
#[global]
Hint Immediate INR_not_0: real.

Lemma not_0_INR : forall n:nat, n <> 0%nat -> INR n <> 0.
Proof.
  intros [| n'] H.
  - now exfalso; apply H.
  - rewrite S_INR; apply Rgt_not_eq.
    now apply Rplus_le_lt_0_compat with (1 := (pos_INR n')); apply Rlt_0_1.
Qed.
#[global]
Hint Resolve not_0_INR: real.

Lemma not_INR : forall n m:nat, n <> m -> INR n <> INR m.
Proof.
  intros n m [Hlt | Hgt]%Nat.lt_gt_cases.
  - now apply Rlt_not_eq, lt_INR.
  - now apply not_eq_sym, Rlt_not_eq, lt_INR.
Qed.
#[global]
Hint Resolve not_INR: real.

Lemma INR_eq : forall n m:nat, INR n = INR m -> n = m.
Proof.
  intros n m HR.
  destruct (Nat.eq_dec n m) as [E | NE]; [assumption |].
  now apply not_INR in NE.
Qed.

Lemma INR_le : forall n m:nat, INR n <= INR m -> (n <= m)%nat.
Proof.
  intros n m [I | E].
  - now apply Nat.lt_le_incl, INR_lt.
  - now apply Nat.eq_le_incl, INR_eq.
Qed.
#[global]
Hint Resolve INR_le: real.

Lemma not_1_INR : forall n:nat, n <> 1%nat -> INR n <> 1.
Proof. now intros n; apply not_INR. Qed.
#[global]
Hint Resolve not_1_INR: real.

(*********************************************************)
(** ** Injection from [positive] to [R]                  *)
(*********************************************************)

(* NOTES:
   - IPR is defined in Rdefinitions, using an auxiliary recursive function
     IPR_2.
   - positive is the type of positive integers represented in binary. Its 3
     constructors are
     * xH : positive, represents 1
     * xO : positive -> positive, add a bit 0 at the end (i.e. multiply by 2)
     * xI : positive -> positive, add a bit 1 at the end
            (i.e. multiply by 2 and add 1)
     1 is a notation for xH, p~0 is a notation for (xO p),
     p~1 is a notation for (xI p).
   - definition of positive (and Z) is in Numbers/BinNums.v
   - operations and lemmas are in PArith (modules Pos and Pos2Nat)
   - Pos.peano_ind gives an alternative induction principle using Pos.succ. *)
Lemma IPR_2_xH : IPR_2 xH = 2.
Proof. reflexivity. Qed.

Lemma IPR_2_xO : forall p : positive, IPR_2 (p~0) = 2 * (IPR_2 p).
Proof. now intros p. Qed.

Lemma IPR_2_xI : forall p : positive, IPR_2 (p~1) = 2 * (IPR_2 p) + 2.
Proof.
  intros p; simpl.
  rewrite (Rplus_comm _ 2), <-(Rmult_1_r 2) at 1.
  now rewrite <-(Rmult_plus_distr_l 2).
Qed.

Lemma IPR_xH : IPR xH = 1.
Proof. reflexivity. Qed.

Lemma IPR_IPR_2 : forall p : positive, 2 * IPR p = IPR_2 p.
Proof.
  unfold IPR; intros [p | p |].
  - rewrite IPR_2_xI, Rplus_comm, Rmult_plus_distr_l.
    now rewrite <-(Rmult_1_r 2) at 4.
  - now rewrite IPR_2_xO.
  - now rewrite IPR_2_xH, Rmult_1_r.
Qed.

Lemma IPR_xO : forall p : positive, IPR (p~0) = 2 * IPR p.
Proof.
  intros p.
  apply (Rmult_eq_reg_l 2); cycle 1.
  { apply not_eq_sym, Rlt_not_eq, Rlt_0_2. }
  now rewrite 2IPR_IPR_2, IPR_2_xO.
Qed.

Lemma IPR_xI : forall p : positive, IPR (p~1) = 2 * IPR p + 1.
Proof.
  intros p.
  apply (Rmult_eq_reg_l 2); cycle 1.
  { apply not_eq_sym, Rlt_not_eq, Rlt_0_2. }
  now rewrite 2IPR_IPR_2, IPR_2_xI, Rmult_plus_distr_l, Rmult_1_r.
Qed.

Lemma INR_IPR : forall p, INR (Pos.to_nat p) = IPR p.
Proof.
  induction p as [p IH | p IH |].
  - now rewrite Pos2Nat.inj_xI, IPR_xI, S_INR, mult_INR, IH.
  - now rewrite Pos2Nat.inj_xO, mult_INR, IPR_xO, IH.
  - reflexivity.
Qed.

Lemma succ_IPR : forall p, IPR (Pos.succ p) = IPR 1 + IPR p.
Proof.
  induction p as [p IH |p IH |].
  - simpl; rewrite IPR_xO, IPR_xI, IH, IPR_xH, Rmult_plus_distr_l.
    now rewrite (Rplus_comm 1), (Rplus_assoc _ 1), Rplus_diag, Rplus_comm.
  - now simpl; rewrite IPR_xI, IPR_xO, IPR_xH, Rplus_comm.
  - now simpl; rewrite IPR_xO, <-Rplus_diag.
Qed.

Lemma plus_IPR : forall p q, IPR (p + q) = IPR p + IPR q.
Proof.
  intros p q; induction q as [| q IH] using Pos.peano_ind.
  - now rewrite Pos.add_1_r, succ_IPR, Rplus_comm.
  - rewrite Pos.add_succ_r, 2succ_IPR, IH.
    now rewrite <-Rplus_assoc, (Rplus_comm (IPR 1)), Rplus_assoc.
Qed.

Lemma minus_IPR : forall p q, (q < p)%positive -> IPR (p - q) = IPR p - IPR q.
Proof.
  induction p as [| p IH] using Pos.peano_ind.
  - now intros q H%Pos.nlt_1_r.
  - intros q H; destruct q as [| q] using Pos.peano_ind.
    + now rewrite succ_IPR, <-Pos.add_1_r, Pos.add_sub, IPR_xH, Rplus_minus_l.
    + rewrite 2succ_IPR, IPR_xH, Rminus_plus_l_l.
      rewrite <-2Pos.add_1_r, (Pos.add_comm q).
      rewrite Pos.sub_add_distr by (now rewrite Pos.add_1_l, Pos.add_1_r).
      now rewrite Pos.add_sub, IH by (now apply Pos.succ_lt_mono).
Qed.

Lemma mult_IPR : forall p q:positive, IPR (p * q) = IPR p * IPR q.
Proof.
  intros p q; induction q as [| q IH] using Pos.peano_ind.
  - now rewrite Pos.mul_1_r, IPR_xH, Rmult_1_r.
  - now rewrite Pos.mul_succ_r, succ_IPR, plus_IPR, IH,
      Rmult_plus_distr_l, Rmult_1_r.
Qed.

Lemma pow_IPR (q p: positive) : IPR (q ^ p) = pow (IPR q) (Pos.to_nat p).
Proof.
  induction p as [| p IH] using Pos.peano_ind.
  - now simpl; rewrite Pos.pow_1_r, Rmult_1_r.
  - now rewrite Pos.pow_succ_r, mult_IPR, Pos2Nat.inj_succ; simpl; rewrite IH.
Qed.

Lemma IPR_ge_1 : forall p:positive, 1 <= IPR p.
Proof.
  pose proof (Rlt_0_1) as H; pose proof (Rlt_0_2) as H'.
  induction p as [p IH | p IH |].
  - rewrite IPR_xI, <-(Rplus_0_l 1) at 1; apply Rplus_le_compat_r.
    apply Rmult_le_pos; try now left.
    now apply (Rle_trans _ 1); try apply IH; left.
  - rewrite IPR_xO, <-Rplus_diag, <-(Rplus_0_l 1); apply Rplus_le_compat; try easy.
    now apply (Rle_trans _ 1); try apply IH; left.
  - now rewrite IPR_xH; apply Rle_refl.
Qed.

Lemma IPR_gt_0 : forall p:positive, 0 < IPR p.
Proof.
  now intros p; apply (Rlt_le_trans _ 1); [apply Rlt_0_1 | apply IPR_ge_1].
Qed.

Lemma lt_IPR : forall p q:positive, (p < q)%positive -> IPR p < IPR q.
Proof.
  pose proof IPR_gt_0 as H; pose proof Rlt_0_2 as H'.
  induction p as [| p IH] using Pos.peano_ind; intros q Hq.
  - rewrite IPR_xH; induction q as [q IH' | [ q | q |] IH' |].
    + rewrite IPR_xI, <-(Rplus_0_l 1) at 1.
      now apply Rplus_lt_compat_r, Rmult_lt_0_compat.
    + rewrite IPR_xO, <-(Rplus_0_l 1), <-Rplus_diag.
      apply Rplus_lt_compat; try easy; apply IH'; constructor.
    + rewrite IPR_xO, <-(Rplus_0_l 1), <-Rplus_diag.
      apply Rplus_lt_compat; try easy; apply IH'; constructor.
    + rewrite IPR_xO, IPR_xH.
      rewrite <-(Rplus_0_l 1) at 1; rewrite <-Rplus_diag.
      now apply Rplus_lt_compat_r, Rlt_0_1.
    + discriminate.
  - destruct q as [| q'] using Pos.peano_ind.
    + now exfalso; apply (Pos.nlt_1_r (Pos.succ p)).
    + now rewrite 2 succ_IPR; apply Rplus_lt_compat_l, IH, Pos.succ_lt_mono.
Qed.

Lemma lt_1_IPR : forall p:positive, (1 < p)%positive -> 1 < IPR p.
Proof. now apply lt_IPR. Qed.

Lemma IPR_lt : forall p q:positive, IPR p < IPR q -> (p < q)%positive.
Proof.
  intros p q. generalize dependent p.
  induction q as [| q IH] using Pos.peano_ind; intros p H.
  - rewrite IPR_xH in H; exfalso; apply (Rle_not_lt (IPR p) 1); try easy.
    now apply IPR_ge_1.
  - destruct p as [| p] using Pos.peano_ind.
    + exact (Pos.lt_1_succ q).
    + apply ->Pos.succ_lt_mono; apply IH.
      rewrite 2!succ_IPR in H.
      now apply Rplus_lt_reg_l with (1 := H).
Qed.

Lemma le_IPR : forall p q:positive, (p <= q)%positive -> IPR p <= IPR q.
Proof.
  intros p q [I | ->]%Pos.le_lteq.
  - now left; apply lt_IPR.
  - now right.
Qed.

Lemma IPR_not_1 : forall p:positive, IPR p <> 1 -> p <> 1%positive.
Proof. now intros p H ->; apply H, IPR_xH. Qed.

Lemma not_1_IPR : forall p:positive, p <> 1%positive -> IPR p <> 1.
Proof.
  intros p H; destruct p as [| p] using Pos.peano_ind.
  - now exfalso; apply H.
  - rewrite succ_IPR; apply Rgt_not_eq.
    rewrite <-(Rplus_0_r 1), IPR_xH.
    now apply Rplus_gt_compat_l, IPR_gt_0.
Qed.

Lemma not_IPR : forall p q:positive, p <> q -> IPR p <> IPR q.
Proof.
  intros p q.
  destruct (Pos.lt_total p q) as [Hlt | [Eq | Hgt]]; intros H.
  - now apply Rlt_not_eq, lt_IPR.
  - easy.
  - now apply not_eq_sym, Rlt_not_eq, lt_IPR.
Qed.

Lemma IPR_eq : forall p q:positive, IPR p = IPR q -> p = q.
Proof.
  intros p q HR.
  destruct (Pos.eq_dec p q) as [E | NE]; [assumption |].
  now apply not_IPR in NE.
Qed.

Lemma IPR_le : forall p q:positive, IPR p <= IPR q -> (p <= q)%positive.
Proof.
  intros p q [I | E].
  - now apply Pos.lt_le_incl, IPR_lt.
  - now apply IPR_eq in E as ->; apply Pos.le_refl.
Qed.

(*********************************************************)
(** ** Injection from [Z] to [R]                         *)
(*********************************************************)
(* NOTES:
   - Z has 3 constructors :
     * Z0 : Z, representing 0
     * Zpos : positive -> Z, for a positive integer
     * Zneg : positive -> Z, for a negative integer
   - Definition of Z is in Numbers.BinNums
   - Operations and lemmas are in ZArith (modules Z, Z2Nat, Nat2Z)
*)
Lemma IZN : forall n:Z, (0 <= n)%Z -> exists m : nat, n = Z.of_nat m.
Proof. now intros n H%Z2Nat.id; exists (Z.to_nat n). Qed.

Lemma INR_IZR_INZ : forall n:nat, INR n = IZR (Z.of_nat n).
Proof.
  intros [| n].
  - reflexivity.
  - simpl Z.of_nat; unfold IZR; simpl IZR.
    now rewrite <-INR_IPR, SuccNat2Pos.id_succ.
Qed.

Lemma IZR_NEG : forall p, IZR (Zneg p) = Ropp (IZR (Zpos p)).
Proof. reflexivity. Qed.

(** The three following lemmas map the default form of numerical
    constants to their representation in terms of the axioms of
    [R]. This can be a useful intermediate representation for reifying
    to another axiomatics of the reals. It is however generally more
    convenient to keep constants represented under an [IZR z] form when
    working within [R]. *)

Lemma IZR_POS_xO : forall p, IZR (Zpos (p~0)) = 2 * (IZR (Zpos p)).
Proof.
  now unfold IZR, IPR; intros [p | p |]; simpl; try easy; rewrite Rmult_1_r.
Qed.

Lemma IZR_POS_xI : forall p, IZR (Zpos (xI p)) = 1 + 2 * IZR (Zpos p).
Proof.
  now unfold IZR, IPR; intros [p | p |]; simpl; try easy; rewrite Rmult_1_r.
Qed.

Lemma plus_IZR_NEG_POS :
  forall p q:positive, IZR (Zpos p + Zneg q) = IZR (Zpos p) + IZR (Zneg q).
Proof.
  unfold IZR; intros p q; simpl; rewrite Z.pos_sub_spec.
  destruct (Pos.compare_spec p q) as [-> | Lt | Gt].
  - now rewrite Rplus_opp_r.
  - rewrite minus_IPR by (exact Lt); rewrite Ropp_minus_distr.
    now unfold Rminus; rewrite Rplus_comm.
  - now rewrite minus_IPR by (exact Gt); unfold Rminus.
Qed.

Lemma plus_IZR : forall n m:Z, IZR (n + m) = IZR n + IZR m.
Proof.
  intros [| p | p] [| q | q];
    rewrite ?Rplus_0_l, ?Rplus_0_r, ?Z.add_0_l, ?Z.add_0_r; try easy.
  - now unfold IZR; simpl; apply plus_IPR.
  - now apply plus_IZR_NEG_POS.
  - now rewrite Rplus_comm, Z.add_comm; apply plus_IZR_NEG_POS.
  - now unfold IZR; simpl; rewrite plus_IPR, Ropp_plus_distr.
Qed.

Lemma mult_IZR : forall n m:Z, IZR (n * m) = IZR n * IZR m.
Proof.
  intros [| p | p] [| q | q];
    rewrite ?Rmult_0_l, ?Rmult_0_r, ?Z.mul_0_l, ?Z.mul_0_r; try easy;
      unfold IZR; simpl.
  - now apply mult_IPR.
  - now rewrite mult_IPR, Ropp_mult_distr_r.
  - now rewrite mult_IPR, Ropp_mult_distr_l.
  - now rewrite mult_IPR, Rmult_opp_opp.
Qed.

Lemma pow_IZR : forall z n, pow (IZR z) n = IZR (Z.pow z (Z.of_nat n)).
Proof.
  intros z; induction n as [| n IH].
  - reflexivity.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by (apply Nat2Z.is_nonneg).
    now simpl; rewrite IH, mult_IZR.
Qed.

Lemma succ_IZR : forall n:Z, IZR (Z.succ n) = IZR n + 1.
Proof. now intros n; unfold Z.succ; apply plus_IZR. Qed.

Lemma opp_IZR : forall n:Z, IZR (- n) = - IZR n.
Proof.
  intros [| p | p]; unfold IZR; simpl.
  - now replace R0 with 0 by reflexivity; rewrite Ropp_0.
  - reflexivity.
  - now rewrite Ropp_involutive.
Qed.

Definition Ropp_Ropp_IZR := opp_IZR.

Lemma minus_IZR : forall n m:Z, IZR (n - m) = IZR n - IZR m.
Proof.
  now intros n m; unfold Z.sub, Rminus; rewrite <-opp_IZR; apply plus_IZR.
Qed.

Lemma Z_R_minus : forall n m:Z, IZR n - IZR m = IZR (n - m).
Proof.
  intros z1 z2; unfold Rminus, Z.sub.
  now rewrite <-(Ropp_Ropp_IZR z2); symmetry; apply plus_IZR.
Qed.

Lemma lt_0_IZR : forall n:Z, 0 < IZR n -> (0 < n)%Z.
Proof.
  intros [| p | p]; simpl; intros H.
  - destruct (Rlt_irrefl _ H).
  - now constructor.
  - destruct (Rlt_not_le _ _ H); unfold IZR; replace R0 with 0 by reflexivity.
    rewrite <-Ropp_0; apply Ropp_le_contravar, Rle_trans with (1 := Rle_0_1).
    now apply IPR_ge_1.
Qed.

Lemma lt_IZR : forall n m:Z, IZR n < IZR m -> (n < m)%Z.
Proof.
  intros z1 z2 H; apply Z.lt_0_sub.
  apply lt_0_IZR.
  rewrite <- Z_R_minus.
  exact (Rgt_minus (IZR z2) (IZR z1) H).
Qed.

Lemma eq_IZR_R0 : forall n:Z, IZR n = 0 -> n = 0%Z.
Proof.
  intros [| p | p]; unfold IZR; simpl; intros H; try easy.
  - exfalso; apply (Rlt_not_eq 0 (IPR p)); try easy; apply IPR_gt_0.
  - exfalso; apply (Rlt_not_eq 0 (IPR p)); try apply IPR_gt_0; symmetry.
    replace R0 with 0 in H by reflexivity; rewrite <-Ropp_0 in H.
    now apply Ropp_eq_reg.
Qed.

Lemma eq_IZR : forall n m:Z, IZR n = IZR m -> n = m.
Proof.
  intros n m H%(Rminus_diag_eq); rewrite Z_R_minus in H.
  now apply Zminus_eq, eq_IZR_R0.
Qed.

Lemma not_0_IZR : forall n:Z, n <> 0%Z -> IZR n <> 0.
Proof. now intros z H H'; apply H, eq_IZR. Qed.

Lemma le_0_IZR : forall n:Z, 0 <= IZR n -> (0 <= n)%Z.
Proof.
  unfold Rle; intros n [H | ->%eq_sym%eq_IZR_R0].
  - now apply Z.lt_le_incl, lt_0_IZR.
  - now apply Z.le_refl.
Qed.

Lemma le_IZR : forall n m:Z, IZR n <= IZR m -> (n <= m)%Z.
Proof.
  unfold Rle; intros n m [H%lt_IZR | ->%eq_IZR].
  - now apply Z.lt_le_incl.
  - now apply Z.le_refl.
Qed.

(* NOTE: 1 is a notation for (IZR 1) *)
Lemma le_IZR_R1 : forall n:Z, IZR n <= 1 -> (n <= 1)%Z.
Proof. now intros n; apply le_IZR. Qed.

Lemma IZR_ge : forall n m:Z, (n >= m)%Z -> IZR n >= IZR m.
Proof.
  intros n m H; apply Rnot_lt_ge; intros H2%lt_IZR.
  now apply (Zle_not_lt n m).
Qed.

Lemma IZR_le : forall n m:Z, (n <= m)%Z -> IZR n <= IZR m.
Proof. now intros m n H%Z.le_ge; apply Rge_le, IZR_ge. Qed.

Lemma IZR_lt : forall n m:Z, (n < m)%Z -> IZR n < IZR m.
Proof.
  intros n m H; apply Rnot_le_lt; intros [I | E%eq_IZR].
  - now apply (Z.lt_irrefl m), Z.lt_trans with (2 := H), lt_IZR.
  - now apply (Z.lt_irrefl m); rewrite E at 1.
Qed.

Lemma eq_IZR_contrapositive : forall n m:Z, n <> m -> IZR n <> IZR m.
Proof. now intros n m H1 H2%eq_IZR. Qed.

#[global]
Hint Extern 0 (IZR _ <= IZR _) => apply IZR_le, Zle_bool_imp_le, eq_refl : real.
#[global]
Hint Extern 0 (IZR _ >= IZR _) => apply Rle_ge, IZR_le, Zle_bool_imp_le, eq_refl : real.
#[global]
Hint Extern 0 (IZR _ <  IZR _) => apply IZR_lt, eq_refl : real.
#[global]
Hint Extern 0 (IZR _ >  IZR _) => apply IZR_lt, eq_refl : real.
Lemma Private_Zeq_bool_neq : forall x y : Z, (x =? y) = false -> x <> y.
Proof. intros. rewrite <-Z.eqb_eq. congruence. Qed.
#[global]
Hint Extern 0 (IZR _ <> IZR _) => apply eq_IZR_contrapositive, Private_Zeq_bool_neq, eq_refl : real.

Lemma one_IZR_lt1 : forall n:Z, -1 < IZR n < 1 -> n = 0%Z.
Proof.
  intros n [H1 H2]; apply Z.le_antisymm.
  - now apply Z.lt_succ_r; apply lt_IZR.
  - replace 0%Z with (Z.succ (-1)) by reflexivity.
    now apply Z.le_succ_l, lt_IZR.
Qed.

Lemma one_IZR_r_R1 :
  forall r (n m:Z), r < IZR n <= r + 1 -> r < IZR m <= r + 1 -> n = m.
Proof.
  intros r n m [H1 H2] [H3 H4]; apply Zminus_eq, one_IZR_lt1.
  rewrite <-Z_R_minus; split.
  - replace (-1) with (r - (r + 1)) by
      (now rewrite Rminus_plus_distr, Rminus_diag, Rminus_0_l).
    unfold Rminus; apply Rplus_lt_le_compat; [assumption |].
    now apply Ropp_le_contravar.
  - replace 1 with (r + 1 - r) by (now apply Rplus_minus_l).
    unfold Rminus; apply Rplus_le_lt_compat; try easy.
    now apply Ropp_lt_contravar.
Qed.

Lemma INR_unbounded : forall A, exists n, INR n > A.
Proof.
  intros A; destruct (Rle_or_lt 0 A) as [A_ge0 | A_lt0]; cycle 1.
  { now exists 0%nat; simpl. }
  destruct (archimed A) as [ar1 _].
  exists (Z.to_nat (up A)).
  rewrite INR_IZR_INZ, Z2Nat.id; try assumption.
  apply le_IZR, Rle_trans with (1 := A_ge0).
  now left.
Qed.

Lemma INR_archimed :
  forall eps A : R, eps > 0 -> exists n : nat, (INR n) * eps > A.
Proof.
  intros eps A Heps; destruct (INR_unbounded (A / eps)) as [N HN].
  exists N.
  apply (Rmult_gt_reg_r (/ eps)).
  { now apply Rinv_0_lt_compat. }
  now rewrite Rmult_assoc, Rinv_r by (now apply Rgt_not_eq); rewrite Rmult_1_r.
Qed.

Lemma R_rm : ring_morph
  0%R 1%R Rplus Rmult Rminus Ropp eq
  0%Z 1%Z Zplus Zmult Zminus Z.opp Z.eqb IZR.
Proof.
  constructor; try easy.
  - exact plus_IZR.
  - exact minus_IZR.
  - exact mult_IZR.
  - exact opp_IZR.
  - now intros x y H; f_equal; apply Z.eqb_eq.
Qed.

(* NOTE: keeping inconsistent variable names for backward compatibility. *)
#[deprecated(use=Z.eqb_eq, since="9.0")]
Lemma Zeq_bool_IZR : forall x y:Z, IZR x = IZR y -> Z.eqb x y = true.
Proof. now intros n m H; apply Z.eqb_eq, eq_IZR. Qed.

Local Lemma Private_Zeqb_IZR : forall x y:Z, IZR x = IZR y -> Z.eqb x y = true.
Proof. intros. apply Z.eqb_eq, eq_IZR; trivial. Qed.

Add Field RField : Rfield
  (completeness Private_Zeqb_IZR, morphism R_rm, constants [IZR_tac], power_tac R_power_theory [Rpow_tac]).

(*********************************************************)
(** * Definitions of new types                           *)
(*********************************************************)

Record nonnegreal : Type := mknonnegreal
  {nonneg :> R; cond_nonneg : 0 <= nonneg}.

Record posreal : Type := mkposreal {pos :> R; cond_pos : 0 < pos}.

Record nonposreal : Type := mknonposreal
  {nonpos :> R; cond_nonpos : nonpos <= 0}.

Record negreal : Type := mknegreal {neg :> R; cond_neg : neg < 0}.

Record nonzeroreal : Type := mknonzeroreal
  {nonzero :> R; cond_nonzero : nonzero <> 0}.

(** ** A few common instances *)

Lemma pos_half_prf : 0 < / 2.
Proof. now apply Rinv_0_lt_compat, Rlt_0_2. Qed.

Definition posreal_one := mkposreal (1) (Rlt_0_1).
Definition posreal_half := mkposreal (/ 2) pos_half_prf.

(** * Compatibility *)

Notation prod_neq_R0 := Rmult_integral_contrapositive_currified (only parsing).
Notation minus_Rgt := Rminus_gt (only parsing).
Notation minus_Rge := Rminus_ge (only parsing).
Notation plus_le_is_le := Rplus_le_reg_pos_r (only parsing).
Notation plus_lt_is_lt := Rplus_lt_reg_pos_r (only parsing).
Notation INR_lt_1 := lt_1_INR (only parsing).
Notation lt_INR_0 := lt_0_INR (only parsing).
Notation not_nm_INR := not_INR (only parsing).
Notation INR_pos := pos_INR_nat_of_P (only parsing).
Notation not_INR_O := INR_not_0 (only parsing).
Notation not_O_INR := not_0_INR (only parsing).
Notation not_O_IZR := not_0_IZR (only parsing).
Notation le_O_IZR := le_0_IZR (only parsing).
Notation lt_O_IZR := lt_0_IZR (only parsing).

Notation tech_Rplus := Rplus_le_lt_0_neq_0 (only parsing).
Notation tech_Rgt_minus := Rgt_minus_pos (only parsing).
Notation le_epsilon := Rle_plus_epsilon (only parsing).
Notation completeness_weak := upper_bound_thm (only parsing).
Notation Req_EM_T := Req_dec_T (only parsing).
Notation Rinv_r_simpl_r := Rmult_inv_m_id_r (only parsing).
Notation Rinv_r_simpl_l := Rmult_inv_r_id_l (only parsing).
Notation Rinv_r_simpl_m := Rmult_inv_r_id_m (only parsing).
Notation Rplus_eq_R0 := Rplus_eq_0 (only parsing).

Lemma Rinv_involutive_depr : forall r, r <> 0 -> / / r = r.
Proof. now intros r _; apply Rinv_inv.  Qed.
#[deprecated(since="8.16",note="Use Rinv_inv.")]
Notation Rinv_involutive := Rinv_involutive_depr (only parsing).

Lemma Rinv_mult_distr_depr :
  forall r1 r2, r1 <> 0 -> r2 <> 0 -> / (r1 * r2) = / r1 * / r2.
Proof. now intros r1 r2 _ _; apply Rinv_mult. Qed.
#[deprecated(since="8.16",note="Use Rinv_mult.")]
Notation Rinv_mult_distr := Rinv_mult_distr_depr (only parsing).

Lemma Ropp_inv_permute_depr : forall r, r <> 0 -> - / r = / - r.
Proof. now intros r H; apply eq_sym, Rinv_opp. Qed.
#[deprecated(since="8.16",note="Use Rinv_opp.")]
Notation Ropp_inv_permute := Ropp_inv_permute_depr (only parsing).

Lemma Ropp_div_den_depr : forall x y, y <> 0 -> x / - y = - (x / y).
Proof. now intros r1 r2 _; apply Ropp_div_distr_r. Qed.
#[deprecated(since="8.16",note="Use Rdiv_opp_r.")]
Notation Ropp_div_den := Ropp_div_den_depr (only parsing).

Lemma inser_trans_R_depr :
  forall r1 r2 r3 r4, r1 <= r2 < r3 -> {r1 <= r2 < r4} + {r4 <= r2 < r3}.
Proof.
  intros r1 r2 r3 r4 [H1 H2]; destruct (Rlt_le_dec r2 r4) as [Hlt | Hle].
  - now left.
  - now right.
Qed.
#[deprecated(since="8.19")]
Notation inser_trans_R := inser_trans_R_depr (only parsing).

Lemma Ropp_minus_distr'_depr : forall r1 r2, - (r2 - r1) = r1 - r2.
Proof. now intros r1 r2; apply Ropp_minus_distr. Qed.
#[deprecated(since="8.19",note="Use Ropp_minus_distr instead.")]
Notation Ropp_minus_distr' := (fun r1 r2 => (Ropp_minus_distr r2 r1)) (only parsing).

#[deprecated(since="8.19",note="Use Rminus_diag instead.")]
Notation Rminus_eq_0 := (fun x => Rminus_diag x) (only parsing).

Lemma sum_inequa_Rle_lt_depr :
  forall a x b c y d:R,
    a <= x -> x < b -> c < y -> y <= d -> a + c < x + y < b + d.
Proof.
  intros; split.
  - apply Rlt_le_trans with (a + y); auto with real.
  - apply Rlt_le_trans with (b + y); auto with real.
Qed.
#[deprecated(since="8.19")]
Notation sum_inequa_Rle_lt := sum_inequa_Rle_lt_depr (only parsing).

Lemma Rle_Rinv_depr : forall x y:R, 0 < x -> 0 < y -> x <= y -> / y <= / x.
Proof. now intros r1 r2 H _; apply Rinv_le_contravar. Qed.
#[deprecated(since="8.19",note="Use Rinv_le_contravar.")]
Notation Rle_Rinv := Rle_Rinv_depr (only parsing).

#[deprecated(since="8.19",note="Use the bidirectional version Rlt_0_minus instead.")]
Notation Rlt_Rminus := (fun a b => proj2 (Rlt_0_minus a b)) (only parsing).

#[deprecated(since="8.19",note="Use the bidirectional version Rlt_0_minus instead.")]
Notation Rminus_gt_0_lt := (fun a b => proj1 (Rlt_0_minus a b)) (only parsing).

#[deprecated(since="8.19",note="Use Rdiv_opp_l.")]
Notation Ropp_div := (fun x y => Rdiv_opp_l x y) (only parsing).

Lemma Rplus_sqr_eq_0_l_depr : forall r1 r2, Rsqr r1 + Rsqr r2 = 0 -> r1 = 0.
Proof.
  now intros r1 r2 H; apply Rsqr_0_uniq, (Rplus_eq_0_l _ (r2²)); try easy;
    apply Rle_0_sqr.
Qed.
#[deprecated(since="8.19",note="Use Rplus_sqr_eq_0.")]
Notation Rplus_sqr_eq_0_l := Rplus_sqr_eq_0_l_depr (only parsing).

#[deprecated(since="8.19",note="Use Rplus_diag.")]
Notation double := (fun r1 => eq_sym (Rplus_diag r1)) (only parsing).

#[deprecated(since="8.19",note="Use Rplus_half_diag.")]
Notation double_var := (fun r1 => eq_sym (Rplus_half_diag r1)) (only parsing).

#[deprecated(since="8.19",note="Use eq_IZR_contrapositive.")]
Notation IZR_neq := (fun z1 z2 => (eq_IZR_contrapositive z1 z2)) (only parsing).

Lemma S_O_plus_INR_depr : forall n, INR (1 + n) = INR 1 + INR n.
Proof.
  intros [| n'].
  - now rewrite INR_0, Rplus_0_r, Nat.add_0_r.
  - rewrite Rplus_comm; reflexivity.
Qed.
#[deprecated(since="8.19")]
Notation S_O_plus_INR := S_O_plus_INR_depr (only parsing).

Lemma single_z_r_R1_depr :
  forall r (n m:Z),
    r < IZR n -> IZR n <= r + 1 -> r < IZR m -> IZR m <= r + 1 -> n = m.
Proof. now intros r n m Hlt Hle Hlt' Hle'; apply (one_IZR_r_R1 r). Qed.
#[deprecated(since="8.19")]
Notation single_z_r_R1 := single_z_r_R1_depr (only parsing).

Lemma tech_single_z_r_R1_depr :
  forall r (n:Z),
    r < IZR n ->
    IZR n <= r + 1 ->
    (exists s : Z, s <> n /\ r < IZR s /\ IZR s <= r + 1) -> False.
Proof. now intros r z H1 H2 [s [H3 [H4 H5]]]; apply H3, (one_IZR_r_R1 r). Qed.
#[deprecated(since="8.19")]
Notation tech_single_z_r_R1 := tech_single_z_r_R1_depr (only parsing).

Lemma Rinv_mult_simpl_depr :
  forall r1 r2 r3, r1 <> 0 -> r1 * / r2 * (r3 * / r1) = r3 * / r2.
Proof.
  intros r1 r2 r3 r1n0.
  rewrite (Rmult_comm r3 (/ r1)), Rmult_assoc, <-(Rmult_assoc (/ r2)).
  rewrite (Rmult_comm r3), (Rmult_comm (/ r2)), <-2Rmult_assoc.
  now rewrite Rinv_r, Rmult_1_l.
Qed.
#[deprecated(since="8.19")]
Notation Rinv_mult_simpl := Rinv_mult_simpl_depr.
