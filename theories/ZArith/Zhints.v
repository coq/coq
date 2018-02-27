(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file centralizes the lemmas about [Z], classifying them
    according to the way they can be used in automatic search  *)

(** Lemmas which clearly leads to simplification during proof search are *)
(** declared as Hints. A definite status (Hint or not) for the other lemmas *)
(** remains to be given *)

(** Structure of the file *)
(** - simplification lemmas (only those are declared as Hints) *)
(** - reversible lemmas relating operators *)
(** - useful Bottom-up lemmas              *)
(** - irreversible lemmas with meta-variables *)
(** - unclear or too specific lemmas       *)
(** - lemmas to be used as rewrite rules   *)

(** Lemmas involving positive and compare are not taken into account *)

Require Import BinInt.
Require Import Zorder.
Require Import Zmin.
Require Import Zabs.
Require Import Zcompare.
Require Import Znat.
Require Import auxiliary.
Require Import Zmisc.
Require Import Wf_Z.

(************************************************************************)
(** *                 Simplification lemmas                             *)

(** No subgoal or smaller subgoals                                     *)

Hint Resolve
  (** ** Reversible simplification lemmas (no loss of information)      *)
  (** Should clearly be declared as hints                               *)

  (** Lemmas ending by eq *)
  Zsucc_eq_compat (* n = m -> Z.succ n = Z.succ m *)

  (** Lemmas ending by Z.gt *)
  Zsucc_gt_compat (* m > n -> Z.succ m > Z.succ n *)
  Zgt_succ (* Z.succ n > n *)
  Zorder.Zgt_pos_0 (* Z.pos p > 0 *)
  Zplus_gt_compat_l (* n > m -> p+n > p+m *)
  Zplus_gt_compat_r (* n > m -> n+p > m+p *)

  (** Lemmas ending by Z.lt *)
  Pos2Z.is_pos (* 0 < Z.pos p *)
  Z.lt_succ_diag_r (* n < Z.succ n *)
  Zsucc_lt_compat (* n < m -> Z.succ n < Z.succ m *)
  Z.lt_pred_l (* Z.pred n < n *)
  Zplus_lt_compat_l (* n < m -> p+n < p+m *)
  Zplus_lt_compat_r (* n < m -> n+p < m+p *)

  (** Lemmas ending by Z.le *)
  Nat2Z.is_nonneg (* 0 <= Z.of_nat n *)
  Pos2Z.is_nonneg (* 0 <= Z.pos p *)
  Z.le_refl (* n <= n *)
  Z.le_succ_diag_r (* n <= Z.succ n *)
  Zsucc_le_compat (* m <= n -> Z.succ m <= Z.succ n *)
  Z.le_pred_l (* Z.pred n <= n *)
  Z.le_min_l (* Z.min n m <= n *)
  Z.le_min_r (* Z.min n m <= m *)
  Zplus_le_compat_l (* n <= m -> p+n <= p+m *)
  Zplus_le_compat_r (* a <= b -> a+c <= b+c *)
  Z.abs_nonneg (* 0 <= |x| *)

  (** ** Irreversible simplification lemmas *)
  (** Probably to be declared as hints, when no other simplification is possible *)

  (** Lemmas ending by eq *)
  Z_eq_mult (* y = 0 -> y*x = 0 *)
  Zplus_eq_compat (* n = m -> p = q -> n+p = m+q *)

  (** Lemmas ending by Z.ge *)
  Zorder.Zmult_ge_compat_r (* a >= b -> c >= 0 -> a*c >= b*c *)
  Zorder.Zmult_ge_compat_l (* a >= b -> c >= 0 -> c*a >= c*b *)
  Zorder.Zmult_ge_compat (* :
      a >= c -> b >= d -> c >= 0 -> d >= 0 -> a*b >= c*d *)

  (** Lemmas ending by Z.lt *)
  Zorder.Zmult_gt_0_compat (* a > 0 -> b > 0 -> a*b > 0 *)
  Z.lt_lt_succ_r (* n < m -> n < Z.succ m *)

  (** Lemmas ending by Z.le *)
  Z.mul_nonneg_nonneg (* 0 <= x -> 0 <= y -> 0 <= x*y *)
  Zorder.Zmult_le_compat_r (* a <= b -> 0 <= c -> a*c <= b*c *)
  Zorder.Zmult_le_compat_l (* a <= b -> 0 <= c -> c*a <= c*b *)
  Z.add_nonneg_nonneg (* 0 <= x -> 0 <= y -> 0 <= x+y *)
  Z.le_le_succ_r (* x <= y -> x <= Z.succ y *)
  Z.add_le_mono (* n <= m -> p <= q -> n+p <= m+q *)

  : zarith.
