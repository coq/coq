(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Binary Integers (Pierre Crégut, CNET, Lannion, France) *)

Require Export Arith_base.
Require Import BinPos BinInt BinNat Pnat Nnat.

Local Open Scope Z_scope.

(** Conversions between integers and natural numbers

    Seven sections:
    - chains of conversions (combining two conversions)
    - module N2Z : from N to Z
    - module Z2N : from Z to N (negative numbers rounded to 0)
    - module Zabs2N : from Z to N (via the absolute value)
    - module Nat2Z : from nat to Z
    - module Z2Nat : from Z to nat (negative numbers rounded to 0)
    - module Zabs2Nat : from Z to nat (via the absolute value)
*)

(** * Chains of conversions *)

(** When combining successive conversions, we have the following
    commutative diagram:
<<
      ---> Nat ----
     |      ^      |
     |      |      v
    Pos ---------> Z
     |      |      ^
     |      v      |
      ----> N -----
>>
*)

Lemma nat_N_Z n : Z.of_N (N.of_nat n) = Z.of_nat n.
Proof.
 now destruct n.
Qed.

Lemma N_nat_Z n : Z.of_nat (N.to_nat n) = Z.of_N n.
Proof.
 destruct n; trivial. simpl.
 destruct (Pos2Nat.is_succ p) as (m,H).
 rewrite H. simpl. f_equal. now apply SuccNat2Pos.inv.
Qed.

Lemma positive_nat_Z p : Z.of_nat (Pos.to_nat p) = Zpos p.
Proof.
 destruct (Pos2Nat.is_succ p) as (n,H).
 rewrite H. simpl. f_equal. now apply SuccNat2Pos.inv.
Qed.

Lemma positive_N_Z p : Z.of_N (Npos p) = Zpos p.
Proof.
 reflexivity.
Qed.

Lemma positive_N_nat p : N.to_nat (Npos p) = Pos.to_nat p.
Proof.
 reflexivity.
Qed.

Lemma positive_nat_N p : N.of_nat (Pos.to_nat p) = Npos p.
Proof.
 destruct (Pos2Nat.is_succ p) as (n,H).
 rewrite H. simpl. f_equal. now apply SuccNat2Pos.inv.
Qed.

Lemma Z_N_nat n : N.to_nat (Z.to_N n) = Z.to_nat n.
Proof.
 now destruct n.
Qed.

Lemma Z_nat_N n : N.of_nat (Z.to_nat n) = Z.to_N n.
Proof.
 destruct n; simpl; trivial. apply positive_nat_N.
Qed.

Lemma Zabs_N_nat n : N.to_nat (Z.abs_N n) = Z.abs_nat n.
Proof.
 now destruct n.
Qed.

Lemma Zabs_nat_N n : N.of_nat (Z.abs_nat n) = Z.abs_N n.
Proof.
 destruct n; simpl; trivial; apply positive_nat_N.
Qed.


(** * Conversions between [Z] and [N] *)

Module N2Z.

(** [Z.of_N] is a bijection between [N] and non-negative [Z],
    with [Z.to_N] (or [Z.abs_N]) as reciprocal.
    See [Z2N.id] below for the dual equation. *)

Lemma id n : Z.to_N (Z.of_N n) = n.
Proof.
 now destruct n.
Qed.

(** [Z.of_N] is hence injective *)

Lemma inj n m : Z.of_N n = Z.of_N m -> n = m.
Proof.
 destruct n, m; simpl; congruence.
Qed.

Lemma inj_iff n m : Z.of_N n = Z.of_N m <-> n = m.
Proof.
 split. apply inj. intros; now f_equal.
Qed.

(** [Z.of_N] produce non-negative integers *)

Lemma is_nonneg n : 0 <= Z.of_N n.
Proof.
 now destruct n.
Qed.

(** [Z.of_N], basic equations *)

Lemma inj_0 : Z.of_N 0 = 0.
Proof.
 reflexivity.
Qed.

Lemma inj_pos p : Z.of_N (Npos p) = Zpos p.
Proof.
 reflexivity.
Qed.

(** [Z.of_N] and usual operations. *)

Lemma inj_compare n m : (Z.of_N n ?= Z.of_N m) = (n ?= m)%N.
Proof.
 now destruct n, m.
Qed.

Lemma inj_le n m : (n<=m)%N <-> Z.of_N n <= Z.of_N m.
Proof.
 unfold Z.le. now rewrite inj_compare.
Qed.

Lemma inj_lt n m : (n<m)%N <-> Z.of_N n < Z.of_N m.
Proof.
 unfold Z.lt. now rewrite inj_compare.
Qed.

Lemma inj_ge n m : (n>=m)%N <-> Z.of_N n >= Z.of_N m.
Proof.
 unfold Z.ge. now rewrite inj_compare.
Qed.

Lemma inj_gt n m : (n>m)%N <-> Z.of_N n > Z.of_N m.
Proof.
 unfold Z.gt. now rewrite inj_compare.
Qed.

Lemma inj_abs_N z : Z.of_N (Z.abs_N z) = Z.abs z.
Proof.
 now destruct z.
Qed.

Lemma inj_add n m : Z.of_N (n+m) = Z.of_N n + Z.of_N m.
Proof.
 now destruct n, m.
Qed.

Lemma inj_mul n m : Z.of_N (n*m) = Z.of_N n * Z.of_N m.
Proof.
 now destruct n, m.
Qed.

Lemma inj_sub_max n m : Z.of_N (n-m) = Z.max 0 (Z.of_N n - Z.of_N m).
Proof.
 destruct n as [|n], m as [|m]; simpl; trivial.
 rewrite Z.pos_sub_spec, Pos.compare_sub_mask. unfold Pos.sub.
 now destruct (Pos.sub_mask n m).
Qed.

Lemma inj_sub n m : (m<=n)%N -> Z.of_N (n-m) = Z.of_N n - Z.of_N m.
Proof.
 intros H. rewrite inj_sub_max.
 unfold N.le in H.
 rewrite N.compare_antisym, <- inj_compare, Z.compare_sub in H.
 destruct (Z.of_N n - Z.of_N m); trivial; now destruct H.
Qed.

Lemma inj_succ n : Z.of_N (N.succ n) = Z.succ (Z.of_N n).
Proof.
 destruct n. trivial. simpl. now rewrite Pos.add_1_r.
Qed.

Lemma inj_pred_max n : Z.of_N (N.pred n) = Z.max 0 (Z.pred (Z.of_N n)).
Proof.
 unfold Z.pred. now rewrite N.pred_sub, inj_sub_max.
Qed.

Lemma inj_pred n : (0<n)%N -> Z.of_N (N.pred n) = Z.pred (Z.of_N n).
Proof.
 intros H. unfold Z.pred. rewrite N.pred_sub, inj_sub; trivial.
 now apply N.le_succ_l in H.
Qed.

Lemma inj_min n m : Z.of_N (N.min n m) = Z.min (Z.of_N n) (Z.of_N m).
Proof.
 unfold Z.min, N.min. rewrite inj_compare. now case N.compare.
Qed.

Lemma inj_max n m : Z.of_N (N.max n m) = Z.max (Z.of_N n) (Z.of_N m).
Proof.
 unfold Z.max, N.max. rewrite inj_compare.
 case N.compare_spec; intros; subst; trivial.
Qed.

Lemma inj_div n m : Z.of_N (n/m) = Z.of_N n / Z.of_N m.
Proof.
 destruct m as [|m]. now destruct n.
 apply Z.div_unique_pos with (Z.of_N (n mod (Npos m))).
 split. apply is_nonneg. apply inj_lt. now apply N.mod_lt.
 rewrite <- inj_mul, <- inj_add. f_equal. now apply N.div_mod.
Qed.

Lemma inj_mod n m : (m<>0)%N -> Z.of_N (n mod m) = (Z.of_N n) mod (Z.of_N m).
Proof.
 intros Hm.
 apply Z.mod_unique_pos with (Z.of_N (n / m)).
 split. apply is_nonneg. apply inj_lt. now apply N.mod_lt.
 rewrite <- inj_mul, <- inj_add. f_equal. now apply N.div_mod.
Qed.

Lemma inj_quot n m : Z.of_N (n/m) = Z.of_N n ÷ Z.of_N m.
Proof.
 destruct m.
 - now destruct n.
 - rewrite Z.quot_div_nonneg, inj_div; trivial. apply is_nonneg. easy.
Qed.

Lemma inj_rem n m : Z.of_N (n mod m) = Z.rem (Z.of_N n) (Z.of_N m).
Proof.
 destruct m.
 - now destruct n.
 - rewrite Z.rem_mod_nonneg, inj_mod; trivial. easy. apply is_nonneg. easy.
Qed.

Lemma inj_div2 n : Z.of_N (N.div2 n) = Z.div2 (Z.of_N n).
Proof.
 destruct n as [|p]; trivial. now destruct p.
Qed.

Lemma inj_quot2 n : Z.of_N (N.div2 n) = Z.quot2 (Z.of_N n).
Proof.
 destruct n as [|p]; trivial. now destruct p.
Qed.

Lemma inj_pow n m : Z.of_N (n^m) = (Z.of_N n)^(Z.of_N m).
Proof.
 destruct n, m; trivial. now rewrite Z.pow_0_l. apply Pos2Z.inj_pow.
Qed.

Lemma inj_testbit a n :
 Z.testbit (Z.of_N a) (Z.of_N n) = N.testbit a n.
Proof. apply Z.testbit_of_N. Qed.

End N2Z.

Module Z2N.

(** [Z.to_N] is a bijection between non-negative [Z] and [N],
    with [Pos.of_N] as reciprocal.
    See [N2Z.id] above for the dual equation. *)

Lemma id n : 0<=n -> Z.of_N (Z.to_N n) = n.
Proof.
 destruct n; (now destruct 1) || trivial.
Qed.

(** [Z.to_N] is hence injective for non-negative integers. *)

Lemma inj n m : 0<=n -> 0<=m -> Z.to_N n = Z.to_N m -> n = m.
Proof.
 intros. rewrite <- (id n), <- (id m) by trivial. now f_equal.
Qed.

Lemma inj_iff n m : 0<=n -> 0<=m -> (Z.to_N n = Z.to_N m <-> n = m).
Proof.
 intros. split. now apply inj. intros; now subst.
Qed.

(** [Z.to_N], basic equations *)

Lemma inj_0 : Z.to_N 0 = 0%N.
Proof.
 reflexivity.
Qed.

Lemma inj_pos n : Z.to_N (Zpos n) = Npos n.
Proof.
 reflexivity.
Qed.

Lemma inj_neg n : Z.to_N (Zneg n) = 0%N.
Proof.
 reflexivity.
Qed.

(** [Z.to_N] and operations *)

Lemma inj_add n m : 0<=n -> 0<=m -> Z.to_N (n+m) = (Z.to_N n + Z.to_N m)%N.
Proof.
 destruct n, m; trivial; (now destruct 1) || (now destruct 2).
Qed.

Lemma inj_mul n m : 0<=n -> 0<=m -> Z.to_N (n*m) = (Z.to_N n * Z.to_N m)%N.
Proof.
 destruct n, m; trivial; (now destruct 1) || (now destruct 2).
Qed.

Lemma inj_succ n : 0<=n -> Z.to_N (Z.succ n) = N.succ (Z.to_N n).
Proof.
 unfold Z.succ. intros. rewrite inj_add by easy. apply N.add_1_r.
Qed.

Lemma inj_sub n m : 0<=m -> Z.to_N (n - m) = (Z.to_N n - Z.to_N m)%N.
Proof.
 destruct n as [|n|n], m as [|m|m]; trivial; try (now destruct 1).
 intros _. simpl.
 rewrite Z.pos_sub_spec, Pos.compare_sub_mask. unfold Pos.sub.
 now destruct (Pos.sub_mask n m).
Qed.

Lemma inj_pred n : Z.to_N (Z.pred n) = N.pred (Z.to_N n).
Proof.
 unfold Z.pred. rewrite <- N.sub_1_r. now apply (inj_sub n 1).
Qed.

Lemma inj_compare n m : 0<=n -> 0<=m ->
 (Z.to_N n ?= Z.to_N m)%N = (n ?= m).
Proof.
 intros Hn Hm. now rewrite <- N2Z.inj_compare, !id.
Qed.

Lemma inj_le n m : 0<=n -> 0<=m -> (n<=m <-> (Z.to_N n <= Z.to_N m)%N).
Proof.
 intros Hn Hm. unfold Z.le, N.le. now rewrite inj_compare.
Qed.

Lemma inj_lt n m : 0<=n -> 0<=m -> (n<m <-> (Z.to_N n < Z.to_N m)%N).
Proof.
 intros Hn Hm. unfold Z.lt, N.lt. now rewrite inj_compare.
Qed.

Lemma inj_min n m : Z.to_N (Z.min n m) = N.min (Z.to_N n) (Z.to_N m).
Proof.
 destruct n, m; simpl; trivial; unfold Z.min, N.min; simpl;
  now case Pos.compare.
Qed.

Lemma inj_max n m : Z.to_N (Z.max n m) = N.max (Z.to_N n) (Z.to_N m).
Proof.
 destruct n, m; simpl; trivial; unfold Z.max, N.max; simpl.
  case Pos.compare_spec; intros; subst; trivial.
  now case Pos.compare.
Qed.

Lemma inj_div n m : 0<=n -> 0<=m -> Z.to_N (n/m) = (Z.to_N n / Z.to_N m)%N.
Proof.
 destruct n, m; trivial; intros Hn Hm;
 (now destruct Hn) || (now destruct Hm) || clear.
 simpl. rewrite <- (N2Z.id (_ / _)). f_equal. now rewrite N2Z.inj_div.
Qed.

Lemma inj_mod n m : 0<=n -> 0<m ->
 Z.to_N (n mod m) = ((Z.to_N n) mod (Z.to_N m))%N.
Proof.
 destruct n, m; trivial; intros Hn Hm;
 (now destruct Hn) || (now destruct Hm) || clear.
 simpl. rewrite <- (N2Z.id (_ mod _)). f_equal. now rewrite N2Z.inj_mod.
Qed.

Lemma inj_quot n m : 0<=n -> 0<=m -> Z.to_N (n÷m) = (Z.to_N n / Z.to_N m)%N.
Proof.
 destruct m.
 - now destruct n.
 - intros. now rewrite Z.quot_div_nonneg, inj_div.
 - now destruct 2.
Qed.

Lemma inj_rem n m :0<=n -> 0<=m ->
 Z.to_N (Z.rem n m) = ((Z.to_N n) mod (Z.to_N m))%N.
Proof.
 destruct m.
 - now destruct n.
 - intros. now rewrite Z.rem_mod_nonneg, inj_mod.
 - now destruct 2.
Qed.

Lemma inj_div2 n : Z.to_N (Z.div2 n) = N.div2 (Z.to_N n).
Proof.
 destruct n as [|p|p]; trivial. now destruct p.
Qed.

Lemma inj_quot2 n : Z.to_N (Z.quot2 n) = N.div2 (Z.to_N n).
Proof.
 destruct n as [|p|p]; trivial; now destruct p.
Qed.

Lemma inj_pow n m : 0<=n -> 0<=m -> Z.to_N (n^m) = ((Z.to_N n)^(Z.to_N m))%N.
Proof.
 destruct m.
 - trivial.
 - intros. now rewrite <- (N2Z.id (_ ^ _)), N2Z.inj_pow, id.
 - now destruct 2.
Qed.

Lemma inj_testbit a n : 0<=n ->
 Z.testbit (Z.of_N a) n = N.testbit a (Z.to_N n).
Proof. apply Z.testbit_of_N'. Qed.

End Z2N.

Module Zabs2N.

(** Results about [Z.abs_N], converting absolute values of [Z] integers
    to [N]. *)

Lemma abs_N_spec n : Z.abs_N n = Z.to_N (Z.abs n).
Proof.
 now destruct n.
Qed.

Lemma abs_N_nonneg n : 0<=n -> Z.abs_N n = Z.to_N n.
Proof.
 destruct n; trivial; now destruct 1.
Qed.

Lemma id_abs n : Z.of_N (Z.abs_N n) = Z.abs n.
Proof.
 now destruct n.
Qed.

Lemma id n : Z.abs_N (Z.of_N n) = n.
Proof.
 now destruct n.
Qed.

(** [Z.abs_N], basic equations *)

Lemma inj_0 : Z.abs_N 0 = 0%N.
Proof.
 reflexivity.
Qed.

Lemma inj_pos p : Z.abs_N (Zpos p) = Npos p.
Proof.
 reflexivity.
Qed.

Lemma inj_neg p : Z.abs_N (Zneg p) = Npos p.
Proof.
 reflexivity.
Qed.

(** [Z.abs_N] and usual operations, with non-negative integers *)

Lemma inj_opp n : Z.abs_N (-n) = Z.abs_N n.
Proof.
 now destruct n.
Qed.

Lemma inj_succ n : 0<=n -> Z.abs_N (Z.succ n) = N.succ (Z.abs_N n).
Proof.
 intros. rewrite !abs_N_nonneg; trivial. now apply Z2N.inj_succ.
 now apply Z.le_le_succ_r.
Qed.

Lemma inj_add n m : 0<=n -> 0<=m -> Z.abs_N (n+m) = (Z.abs_N n + Z.abs_N m)%N.
Proof.
 intros. rewrite !abs_N_nonneg; trivial. now apply Z2N.inj_add.
 now apply Z.add_nonneg_nonneg.
Qed.

Lemma inj_mul n m : Z.abs_N (n*m) = (Z.abs_N n * Z.abs_N m)%N.
Proof.
 now destruct n, m.
Qed.

Lemma inj_sub n m : 0<=m<=n -> Z.abs_N (n-m) = (Z.abs_N n - Z.abs_N m)%N.
Proof.
 intros (Hn,H). rewrite !abs_N_nonneg; trivial. now apply Z2N.inj_sub.
 Z.order.
 now apply Z.le_0_sub.
Qed.

Lemma inj_pred n : 0<n -> Z.abs_N (Z.pred n) = N.pred (Z.abs_N n).
Proof.
 intros. rewrite !abs_N_nonneg. now apply Z2N.inj_pred.
 Z.order.
 apply Z.lt_succ_r. now rewrite Z.succ_pred.
Qed.

Lemma inj_compare n m : 0<=n -> 0<=m ->
 (Z.abs_N n ?= Z.abs_N m)%N = (n ?= m).
Proof.
 intros. rewrite !abs_N_nonneg by trivial. now apply Z2N.inj_compare.
Qed.

Lemma inj_le n m : 0<=n -> 0<=m -> (n<=m <-> (Z.abs_N n <= Z.abs_N m)%N).
Proof.
 intros Hn Hm. unfold Z.le, N.le. now rewrite inj_compare.
Qed.

Lemma inj_lt n m : 0<=n -> 0<=m -> (n<m <-> (Z.abs_N n < Z.abs_N m)%N).
Proof.
 intros Hn Hm. unfold Z.lt, N.lt. now rewrite inj_compare.
Qed.

Lemma inj_min n m : 0<=n -> 0<=m ->
 Z.abs_N (Z.min n m) = N.min (Z.abs_N n) (Z.abs_N m).
Proof.
 intros. rewrite !abs_N_nonneg; trivial. now apply Z2N.inj_min.
 now apply Z.min_glb.
Qed.

Lemma inj_max n m : 0<=n -> 0<=m ->
 Z.abs_N (Z.max n m) = N.max (Z.abs_N n) (Z.abs_N m).
Proof.
 intros. rewrite !abs_N_nonneg; trivial. now apply Z2N.inj_max.
 transitivity n; trivial. apply Z.le_max_l.
Qed.

Lemma inj_quot n m : Z.abs_N (n÷m) = ((Z.abs_N n) / (Z.abs_N m))%N.
Proof.
 assert (forall p q, Z.abs_N (Zpos p ÷ Zpos q) = (Npos p / Npos q)%N).
  intros. rewrite abs_N_nonneg. now apply Z2N.inj_quot. now apply Z.quot_pos.
 destruct n, m; trivial; simpl.
 - trivial.
 - now rewrite <- Pos2Z.opp_pos, Z.quot_opp_r, inj_opp.
 - now rewrite <- Pos2Z.opp_pos, Z.quot_opp_l, inj_opp.
 - now rewrite <- 2 Pos2Z.opp_pos, Z.quot_opp_opp.
Qed.

Lemma inj_rem n m : Z.abs_N (Z.rem n m) = ((Z.abs_N n) mod (Z.abs_N m))%N.
Proof.
 assert
  (forall p q, Z.abs_N (Z.rem (Zpos p) (Zpos q)) = ((Npos p) mod (Npos q))%N).
  intros. rewrite abs_N_nonneg. now apply Z2N.inj_rem. now apply Z.rem_nonneg.
 destruct n, m; trivial; simpl.
 - trivial.
 - now rewrite <- Pos2Z.opp_pos, Z.rem_opp_r.
 - now rewrite <- Pos2Z.opp_pos, Z.rem_opp_l, inj_opp.
 - now rewrite <- 2 Pos2Z.opp_pos, Z.rem_opp_opp, inj_opp.
Qed.

Lemma inj_pow n m : 0<=m -> Z.abs_N (n^m) = ((Z.abs_N n)^(Z.abs_N m))%N.
Proof.
 intros Hm. rewrite abs_N_spec, Z.abs_pow, Z2N.inj_pow, <- abs_N_spec; trivial.
 f_equal. symmetry; now apply abs_N_nonneg. apply Z.abs_nonneg.
Qed.

(** [Z.abs_N] and usual operations, statements with [Z.abs] *)

Lemma inj_succ_abs n : Z.abs_N (Z.succ (Z.abs n)) = N.succ (Z.abs_N n).
Proof.
 destruct n; simpl; trivial; now rewrite Pos.add_1_r.
Qed.

Lemma inj_add_abs n m :
 Z.abs_N (Z.abs n + Z.abs m) = (Z.abs_N n + Z.abs_N m)%N.
Proof.
 now destruct n, m.
Qed.

Lemma inj_mul_abs n m :
 Z.abs_N (Z.abs n * Z.abs m) = (Z.abs_N n * Z.abs_N m)%N.
Proof.
 now destruct n, m.
Qed.

End Zabs2N.


(** * Conversions between [Z] and [nat] *)

Module Nat2Z.

(** [Z.of_nat], basic equations *)

Lemma inj_0 : Z.of_nat 0 = 0.
Proof.
 reflexivity.
Qed.

Lemma inj_succ n : Z.of_nat (S n) = Z.succ (Z.of_nat n).
Proof.
 destruct n. trivial. simpl. apply Pos2Z.inj_succ.
Qed.

(** [Z.of_N] produce non-negative integers *)

Lemma is_nonneg n : 0 <= Z.of_nat n.
Proof.
 now induction n.
Qed.

(** [Z.of_nat] is a bijection between [nat] and non-negative [Z],
    with [Z.to_nat] (or [Z.abs_nat]) as reciprocal.
    See [Z2Nat.id] below for the dual equation. *)

Lemma id n : Z.to_nat (Z.of_nat n) = n.
Proof.
 now rewrite <- nat_N_Z, <- Z_N_nat, N2Z.id, Nat2N.id.
Qed.

(** [Z.of_nat] is hence injective *)

Lemma inj n m : Z.of_nat n = Z.of_nat m -> n = m.
Proof.
 intros H. now rewrite <- (id n), <- (id m), H.
Qed.

Lemma inj_iff n m : Z.of_nat n = Z.of_nat m <-> n = m.
Proof.
 split. apply inj. intros; now f_equal.
Qed.

(** [Z.of_nat] and usual operations *)

Lemma inj_compare n m : (Z.of_nat n ?= Z.of_nat m) = (n ?= m)%nat.
Proof.
 now rewrite <-!nat_N_Z, N2Z.inj_compare, <- Nat2N.inj_compare.
Qed.

Lemma inj_le n m : (n<=m)%nat <-> Z.of_nat n <= Z.of_nat m.
Proof.
 unfold Z.le. now rewrite inj_compare, nat_compare_le.
Qed.

Lemma inj_lt n m : (n<m)%nat <-> Z.of_nat n < Z.of_nat m.
Proof.
 unfold Z.lt. now rewrite inj_compare, nat_compare_lt.
Qed.

Lemma inj_ge n m : (n>=m)%nat <-> Z.of_nat n >= Z.of_nat m.
Proof.
 unfold Z.ge. now rewrite inj_compare, nat_compare_ge.
Qed.

Lemma inj_gt n m : (n>m)%nat <-> Z.of_nat n > Z.of_nat m.
Proof.
 unfold Z.gt. now rewrite inj_compare, nat_compare_gt.
Qed.

Lemma inj_abs_nat z : Z.of_nat (Z.abs_nat z) = Z.abs z.
Proof.
 destruct z; simpl; trivial;
  destruct (Pos2Nat.is_succ p) as (n,H); rewrite H; simpl; f_equal;
   now apply SuccNat2Pos.inv.
Qed.

Lemma inj_add n m : Z.of_nat (n+m) = Z.of_nat n + Z.of_nat m.
Proof.
 now rewrite <- !nat_N_Z, Nat2N.inj_add, N2Z.inj_add.
Qed.

Lemma inj_mul n m : Z.of_nat (n*m) = Z.of_nat n * Z.of_nat m.
Proof.
 now rewrite <- !nat_N_Z, Nat2N.inj_mul, N2Z.inj_mul.
Qed.

Lemma inj_sub_max n m : Z.of_nat (n-m) = Z.max 0 (Z.of_nat n - Z.of_nat m).
Proof.
 now rewrite <- !nat_N_Z, Nat2N.inj_sub, N2Z.inj_sub_max.
Qed.

Lemma inj_sub n m : (m<=n)%nat -> Z.of_nat (n-m) = Z.of_nat n - Z.of_nat m.
Proof.
 rewrite nat_compare_le, Nat2N.inj_compare. intros.
 now rewrite <- !nat_N_Z, Nat2N.inj_sub, N2Z.inj_sub.
Qed.

Lemma inj_pred_max n : Z.of_nat (Nat.pred n) = Z.max 0 (Z.pred (Z.of_nat n)).
Proof.
 now rewrite <- !nat_N_Z, Nat2N.inj_pred, N2Z.inj_pred_max.
Qed.

Lemma inj_pred n : (0<n)%nat -> Z.of_nat (Nat.pred n) = Z.pred (Z.of_nat n).
Proof.
 rewrite nat_compare_lt, Nat2N.inj_compare. intros.
 now rewrite <- !nat_N_Z, Nat2N.inj_pred, N2Z.inj_pred.
Qed.

Lemma inj_min n m : Z.of_nat (Nat.min n m) = Z.min (Z.of_nat n) (Z.of_nat m).
Proof.
 now rewrite <- !nat_N_Z, Nat2N.inj_min, N2Z.inj_min.
Qed.

Lemma inj_max n m : Z.of_nat (Nat.max n m) = Z.max (Z.of_nat n) (Z.of_nat m).
Proof.
 now rewrite <- !nat_N_Z, Nat2N.inj_max, N2Z.inj_max.
Qed.

End Nat2Z.

Module Z2Nat.

(** [Z.to_nat] is a bijection between non-negative [Z] and [nat],
    with [Pos.of_nat] as reciprocal.
    See [nat2Z.id] above for the dual equation. *)

Lemma id n : 0<=n -> Z.of_nat (Z.to_nat n) = n.
Proof.
 intros. now rewrite <- Z_N_nat, <- nat_N_Z, N2Nat.id, Z2N.id.
Qed.

(** [Z.to_nat] is hence injective for non-negative integers. *)

Lemma inj n m : 0<=n -> 0<=m -> Z.to_nat n = Z.to_nat m -> n = m.
Proof.
 intros. rewrite <- (id n), <- (id m) by trivial. now f_equal.
Qed.

Lemma inj_iff n m : 0<=n -> 0<=m -> (Z.to_nat n = Z.to_nat m <-> n = m).
Proof.
 intros. split. now apply inj. intros; now subst.
Qed.

(** [Z.to_nat], basic equations *)

Lemma inj_0 : Z.to_nat 0 = O.
Proof.
 reflexivity.
Qed.

Lemma inj_pos n : Z.to_nat (Zpos n) = Pos.to_nat n.
Proof.
 reflexivity.
Qed.

Lemma inj_neg n : Z.to_nat (Zneg n) = O.
Proof.
 reflexivity.
Qed.

(** [Z.to_nat] and operations *)

Lemma inj_add n m : 0<=n -> 0<=m ->
 Z.to_nat (n+m) = (Z.to_nat n + Z.to_nat m)%nat.
Proof.
 intros. now rewrite <- !Z_N_nat, Z2N.inj_add, N2Nat.inj_add.
Qed.

Lemma inj_mul n m : 0<=n -> 0<=m ->
 Z.to_nat (n*m) = (Z.to_nat n * Z.to_nat m)%nat.
Proof.
 intros. now rewrite <- !Z_N_nat, Z2N.inj_mul, N2Nat.inj_mul.
Qed.

Lemma inj_succ n : 0<=n -> Z.to_nat (Z.succ n) = S (Z.to_nat n).
Proof.
 intros. now rewrite <- !Z_N_nat, Z2N.inj_succ, N2Nat.inj_succ.
Qed.

Lemma inj_sub n m : 0<=m -> Z.to_nat (n - m) = (Z.to_nat n - Z.to_nat m)%nat.
Proof.
 intros. now rewrite <- !Z_N_nat, Z2N.inj_sub, N2Nat.inj_sub.
Qed.

Lemma inj_pred n : Z.to_nat (Z.pred n) = Nat.pred (Z.to_nat n).
Proof.
 now rewrite <- !Z_N_nat, Z2N.inj_pred, N2Nat.inj_pred.
Qed.

Lemma inj_compare n m : 0<=n -> 0<=m ->
 (Z.to_nat n ?= Z.to_nat m)%nat = (n ?= m).
Proof.
 intros Hn Hm. now rewrite <- Nat2Z.inj_compare, !id.
Qed.

Lemma inj_le n m : 0<=n -> 0<=m -> (n<=m <-> (Z.to_nat n <= Z.to_nat m)%nat).
Proof.
 intros Hn Hm. unfold Z.le. now rewrite nat_compare_le, inj_compare.
Qed.

Lemma inj_lt n m : 0<=n -> 0<=m -> (n<m <-> (Z.to_nat n < Z.to_nat m)%nat).
Proof.
 intros Hn Hm. unfold Z.lt. now rewrite nat_compare_lt, inj_compare.
Qed.

Lemma inj_min n m : Z.to_nat (Z.min n m) = Nat.min (Z.to_nat n) (Z.to_nat m).
Proof.
 now rewrite <- !Z_N_nat, Z2N.inj_min, N2Nat.inj_min.
Qed.

Lemma inj_max n m : Z.to_nat (Z.max n m) = Nat.max (Z.to_nat n) (Z.to_nat m).
Proof.
 now rewrite <- !Z_N_nat, Z2N.inj_max, N2Nat.inj_max.
Qed.

End Z2Nat.

Module Zabs2Nat.

(** Results about [Z.abs_nat], converting absolute values of [Z] integers
    to [nat]. *)

Lemma abs_nat_spec n : Z.abs_nat n = Z.to_nat (Z.abs n).
Proof.
 now destruct n.
Qed.

Lemma abs_nat_nonneg n : 0<=n -> Z.abs_nat n = Z.to_nat n.
Proof.
 destruct n; trivial; now destruct 1.
Qed.

Lemma id_abs n : Z.of_nat (Z.abs_nat n) = Z.abs n.
Proof.
 rewrite <-Zabs_N_nat, N_nat_Z. apply Zabs2N.id_abs.
Qed.

Lemma id n : Z.abs_nat (Z.of_nat n) = n.
Proof.
 now rewrite <-Zabs_N_nat, <-nat_N_Z, Zabs2N.id, Nat2N.id.
Qed.

(** [Z.abs_nat], basic equations *)

Lemma inj_0 : Z.abs_nat 0 = 0%nat.
Proof.
 reflexivity.
Qed.

Lemma inj_pos p : Z.abs_nat (Zpos p) = Pos.to_nat p.
Proof.
 reflexivity.
Qed.

Lemma inj_neg p : Z.abs_nat (Zneg p) = Pos.to_nat p.
Proof.
 reflexivity.
Qed.

(** [Z.abs_nat] and usual operations, with non-negative integers *)

Lemma inj_succ n : 0<=n -> Z.abs_nat (Z.succ n) = S (Z.abs_nat n).
Proof.
 intros. now rewrite <- !Zabs_N_nat, Zabs2N.inj_succ, N2Nat.inj_succ.
Qed.

Lemma inj_add n m : 0<=n -> 0<=m ->
 Z.abs_nat (n+m) = (Z.abs_nat n + Z.abs_nat m)%nat.
Proof.
 intros. now rewrite <- !Zabs_N_nat, Zabs2N.inj_add, N2Nat.inj_add.
Qed.

Lemma inj_mul n m : Z.abs_nat (n*m) = (Z.abs_nat n * Z.abs_nat m)%nat.
Proof.
 destruct n, m; simpl; trivial using Pos2Nat.inj_mul.
Qed.

Lemma inj_sub n m : 0<=m<=n ->
 Z.abs_nat (n-m) = (Z.abs_nat n - Z.abs_nat m)%nat.
Proof.
 intros. now rewrite <- !Zabs_N_nat, Zabs2N.inj_sub, N2Nat.inj_sub.
Qed.

Lemma inj_pred n : 0<n -> Z.abs_nat (Z.pred n) = Nat.pred (Z.abs_nat n).
Proof.
 intros. now rewrite <- !Zabs_N_nat, Zabs2N.inj_pred, N2Nat.inj_pred.
Qed.

Lemma inj_compare n m : 0<=n -> 0<=m ->
 (Z.abs_nat n ?= Z.abs_nat m)%nat = (n ?= m).
Proof.
 intros. now rewrite <- !Zabs_N_nat, <- N2Nat.inj_compare, Zabs2N.inj_compare.
Qed.

Lemma inj_le n m : 0<=n -> 0<=m -> (n<=m <-> (Z.abs_nat n <= Z.abs_nat m)%nat).
Proof.
 intros Hn Hm. unfold Z.le. now rewrite nat_compare_le, inj_compare.
Qed.

Lemma inj_lt n m : 0<=n -> 0<=m -> (n<m <-> (Z.abs_nat n < Z.abs_nat m)%nat).
Proof.
 intros Hn Hm. unfold Z.lt. now rewrite nat_compare_lt, inj_compare.
Qed.

Lemma inj_min n m : 0<=n -> 0<=m ->
 Z.abs_nat (Z.min n m) = Nat.min (Z.abs_nat n) (Z.abs_nat m).
Proof.
 intros. now rewrite <- !Zabs_N_nat, Zabs2N.inj_min, N2Nat.inj_min.
Qed.

Lemma inj_max n m : 0<=n -> 0<=m ->
 Z.abs_nat (Z.max n m) = Nat.max (Z.abs_nat n) (Z.abs_nat m).
Proof.
 intros. now rewrite <- !Zabs_N_nat, Zabs2N.inj_max, N2Nat.inj_max.
Qed.

(** [Z.abs_nat] and usual operations, statements with [Z.abs] *)

Lemma inj_succ_abs n : Z.abs_nat (Z.succ (Z.abs n)) = S (Z.abs_nat n).
Proof.
 now rewrite <- !Zabs_N_nat, Zabs2N.inj_succ_abs, N2Nat.inj_succ.
Qed.

Lemma inj_add_abs n m :
 Z.abs_nat (Z.abs n + Z.abs m) = (Z.abs_nat n + Z.abs_nat m)%nat.
Proof.
 now rewrite <- !Zabs_N_nat, Zabs2N.inj_add_abs, N2Nat.inj_add.
Qed.

Lemma inj_mul_abs n m :
 Z.abs_nat (Z.abs n * Z.abs m) = (Z.abs_nat n * Z.abs_nat m)%nat.
Proof.
 now rewrite <- !Zabs_N_nat, Zabs2N.inj_mul_abs, N2Nat.inj_mul.
Qed.

End Zabs2Nat.


(** Compatibility *)

Definition neq (x y:nat) := x <> y.

Lemma inj_neq n m : neq n m -> Zne (Z.of_nat n) (Z.of_nat m).
Proof. intros H H'. now apply H, Nat2Z.inj. Qed.

Lemma Zpos_P_of_succ_nat n : Zpos (Pos.of_succ_nat n) = Z.succ (Z.of_nat n).
Proof (Nat2Z.inj_succ n).

(** For these one, used in omega, a Definition is necessary *)

Definition inj_eq := (f_equal Z.of_nat).
Definition inj_le n m := proj1 (Nat2Z.inj_le n m).
Definition inj_lt n m := proj1 (Nat2Z.inj_lt n m).
Definition inj_ge n m := proj1 (Nat2Z.inj_ge n m).
Definition inj_gt n m := proj1 (Nat2Z.inj_gt n m).

(** For the others, a Notation is fine *)

Notation inj_0 := Nat2Z.inj_0 (only parsing).
Notation inj_S := Nat2Z.inj_succ (only parsing).
Notation inj_compare := Nat2Z.inj_compare (only parsing).
Notation inj_eq_rev := Nat2Z.inj (only parsing).
Notation inj_eq_iff := (fun n m => iff_sym (Nat2Z.inj_iff n m)) (only parsing).
Notation inj_le_iff := Nat2Z.inj_le (only parsing).
Notation inj_lt_iff := Nat2Z.inj_lt (only parsing).
Notation inj_ge_iff := Nat2Z.inj_ge (only parsing).
Notation inj_gt_iff := Nat2Z.inj_gt (only parsing).
Notation inj_le_rev := (fun n m => proj2 (Nat2Z.inj_le n m)) (only parsing).
Notation inj_lt_rev := (fun n m => proj2 (Nat2Z.inj_lt n m)) (only parsing).
Notation inj_ge_rev := (fun n m => proj2 (Nat2Z.inj_ge n m)) (only parsing).
Notation inj_gt_rev := (fun n m => proj2 (Nat2Z.inj_gt n m)) (only parsing).
Notation inj_plus := Nat2Z.inj_add (only parsing).
Notation inj_mult := Nat2Z.inj_mul (only parsing).
Notation inj_minus1 := Nat2Z.inj_sub (only parsing).
Notation inj_minus := Nat2Z.inj_sub_max (only parsing).
Notation inj_min := Nat2Z.inj_min (only parsing).
Notation inj_max := Nat2Z.inj_max (only parsing).

Notation Z_of_nat_of_P := positive_nat_Z (only parsing).
Notation Zpos_eq_Z_of_nat_o_nat_of_P :=
  (fun p => eq_sym (positive_nat_Z p)) (only parsing).

Notation Z_of_nat_of_N := N_nat_Z (only parsing).
Notation Z_of_N_of_nat := nat_N_Z (only parsing).

Notation Z_of_N_eq := (f_equal Z.of_N) (only parsing).
Notation Z_of_N_eq_rev := N2Z.inj (only parsing).
Notation Z_of_N_eq_iff := (fun n m => iff_sym (N2Z.inj_iff n m)) (only parsing).
Notation Z_of_N_compare := N2Z.inj_compare (only parsing).
Notation Z_of_N_le_iff := N2Z.inj_le (only parsing).
Notation Z_of_N_lt_iff := N2Z.inj_lt (only parsing).
Notation Z_of_N_ge_iff := N2Z.inj_ge (only parsing).
Notation Z_of_N_gt_iff := N2Z.inj_gt (only parsing).
Notation Z_of_N_le := (fun n m => proj1 (N2Z.inj_le n m)) (only parsing).
Notation Z_of_N_lt := (fun n m => proj1 (N2Z.inj_lt n m)) (only parsing).
Notation Z_of_N_ge := (fun n m => proj1 (N2Z.inj_ge n m)) (only parsing).
Notation Z_of_N_gt := (fun n m => proj1 (N2Z.inj_gt n m)) (only parsing).
Notation Z_of_N_le_rev := (fun n m => proj2 (N2Z.inj_le n m)) (only parsing).
Notation Z_of_N_lt_rev := (fun n m => proj2 (N2Z.inj_lt n m)) (only parsing).
Notation Z_of_N_ge_rev := (fun n m => proj2 (N2Z.inj_ge n m)) (only parsing).
Notation Z_of_N_gt_rev := (fun n m => proj2 (N2Z.inj_gt n m)) (only parsing).
Notation Z_of_N_pos := N2Z.inj_pos (only parsing).
Notation Z_of_N_abs := N2Z.inj_abs_N (only parsing).
Notation Z_of_N_le_0 := N2Z.is_nonneg (only parsing).
Notation Z_of_N_plus := N2Z.inj_add (only parsing).
Notation Z_of_N_mult := N2Z.inj_mul (only parsing).
Notation Z_of_N_minus := N2Z.inj_sub_max (only parsing).
Notation Z_of_N_succ := N2Z.inj_succ (only parsing).
Notation Z_of_N_min := N2Z.inj_min (only parsing).
Notation Z_of_N_max := N2Z.inj_max (only parsing).
Notation Zabs_of_N := Zabs2N.id (only parsing).
Notation Zabs_N_succ_abs := Zabs2N.inj_succ_abs (only parsing).
Notation Zabs_N_succ := Zabs2N.inj_succ (only parsing).
Notation Zabs_N_plus_abs := Zabs2N.inj_add_abs (only parsing).
Notation Zabs_N_plus := Zabs2N.inj_add (only parsing).
Notation Zabs_N_mult_abs := Zabs2N.inj_mul_abs (only parsing).
Notation Zabs_N_mult := Zabs2N.inj_mul (only parsing).

Theorem inj_minus2 : forall n m:nat, (m > n)%nat -> Z.of_nat (n - m) = 0.
Proof.
 intros. rewrite not_le_minus_0; auto with arith.
Qed.
