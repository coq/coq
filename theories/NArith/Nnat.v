(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Arith_base Compare_dec Sumbool Div2 Min Max.
Require Import BinPos BinNat Pnat.

(** * Conversions from [N] to [nat] *)

Module N2Nat.

(** [N.to_nat] is a bijection between [N] and [nat],
    with [Pos.of_nat] as reciprocal.
    See [Nat2N.id] below for the dual equation. *)

Lemma id a : N.of_nat (N.to_nat a) = a.
Proof.
 destruct a as [| p]; simpl; trivial.
 destruct (Pos2Nat.is_succ p) as (n,H). rewrite H. simpl. f_equal.
 apply Pos2Nat.inj. rewrite H. apply SuccNat2Pos.id_succ.
Qed.

(** [N.to_nat] is hence injective *)

Lemma inj a a' : N.to_nat a = N.to_nat a' -> a = a'.
Proof.
 intro H. rewrite <- (id a), <- (id a'). now f_equal.
Qed.

Lemma inj_iff a a' : N.to_nat a = N.to_nat a' <-> a = a'.
Proof.
 split. apply inj. intros; now subst.
Qed.

(** Interaction of this translation and usual operations. *)

Lemma inj_double a : N.to_nat (N.double a) = 2*(N.to_nat a).
Proof.
 destruct a; simpl N.to_nat; trivial. apply Pos2Nat.inj_xO.
Qed.

Lemma inj_succ_double a : N.to_nat (N.succ_double a) = S (2*(N.to_nat a)).
Proof.
 destruct a; simpl N.to_nat; trivial. apply Pos2Nat.inj_xI.
Qed.

Lemma inj_succ a : N.to_nat (N.succ a) = S (N.to_nat a).
Proof.
 destruct a; simpl; trivial. apply Pos2Nat.inj_succ.
Qed.

Lemma inj_add a a' :
  N.to_nat (a + a') = N.to_nat a + N.to_nat a'.
Proof.
 destruct a, a'; simpl; trivial. apply Pos2Nat.inj_add.
Qed.

Lemma inj_mul a a' :
  N.to_nat (a * a') = N.to_nat a * N.to_nat a'.
Proof.
 destruct a, a'; simpl; trivial. apply Pos2Nat.inj_mul.
Qed.

Lemma inj_sub a a' :
  N.to_nat (a - a') = N.to_nat a - N.to_nat a'.
Proof.
 destruct a as [|a], a' as [|a']; simpl; auto with arith.
 destruct (Pos.compare_spec a a').
 subst. now rewrite Pos.sub_mask_diag, <- minus_n_n.
 rewrite Pos.sub_mask_neg; trivial. apply Pos2Nat.inj_lt in H.
 simpl; symmetry; apply not_le_minus_0; auto with arith.
 destruct (Pos.sub_mask_pos' _ _ H) as (q & -> & Hq).
 simpl. apply plus_minus. now rewrite <- Hq, Pos2Nat.inj_add.
Qed.

Lemma inj_pred a : N.to_nat (N.pred a) = pred (N.to_nat a).
Proof.
 intros. rewrite pred_of_minus, N.pred_sub. apply inj_sub.
Qed.

Lemma inj_div2 a : N.to_nat (N.div2 a) = div2 (N.to_nat a).
Proof.
 destruct a as [|[p|p| ]]; trivial.
 simpl N.to_nat. now rewrite Pos2Nat.inj_xI, div2_double_plus_one.
 simpl N.to_nat. now rewrite Pos2Nat.inj_xO, div2_double.
Qed.

Lemma inj_compare a a' :
 (a ?= a')%N = nat_compare (N.to_nat a) (N.to_nat a').
Proof.
 destruct a, a'; simpl; trivial.
 now destruct (Pos2Nat.is_succ p) as (n,->).
 now destruct (Pos2Nat.is_succ p) as (n,->).
 apply Pos2Nat.inj_compare.
Qed.

Lemma inj_max a a' :
  N.to_nat (N.max a a') = max (N.to_nat a) (N.to_nat a').
Proof.
 unfold N.max. rewrite inj_compare; symmetry.
 case nat_compare_spec; intros H; try rewrite H; auto with arith.
Qed.

Lemma inj_min a a' :
  N.to_nat (N.min a a') = min (N.to_nat a) (N.to_nat a').
Proof.
  unfold N.min; rewrite inj_compare. symmetry.
  case nat_compare_spec; intros H; try rewrite H; auto with arith.
Qed.

Lemma inj_iter a {A} (f:A->A) (x:A) :
  N.iter a f x = nat_iter (N.to_nat a) f x.
Proof.
 destruct a as [|a]. trivial. apply Pos2Nat.inj_iter.
Qed.

End N2Nat.

Hint Rewrite N2Nat.inj_double N2Nat.inj_succ_double
 N2Nat.inj_succ N2Nat.inj_add N2Nat.inj_mul N2Nat.inj_sub
 N2Nat.inj_pred N2Nat.inj_div2 N2Nat.inj_max N2Nat.inj_min
 N2Nat.id
 : Nnat.


(** * Conversions from [nat] to [N] *)

Module Nat2N.

(** [N.of_nat] is an bijection between [nat] and [N],
    with [Pos.to_nat] as reciprocal.
    See [N2Nat.id] above for the dual equation. *)

Lemma id n : N.to_nat (N.of_nat n) = n.
Proof.
 induction n; simpl; trivial. apply SuccNat2Pos.id_succ.
Qed.

Hint Rewrite id : Nnat.
Ltac nat2N := apply N2Nat.inj; now autorewrite with Nnat.

(** [N.of_nat] is hence injective *)

Lemma inj n n' : N.of_nat n = N.of_nat n' -> n = n'.
Proof.
 intros H. rewrite <- (id n), <- (id n'). now f_equal.
Qed.

Lemma inj_iff n n' : N.of_nat n = N.of_nat n' <-> n = n'.
Proof.
 split. apply inj. intros; now subst.
Qed.

(** Interaction of this translation and usual operations. *)

Lemma inj_double n : N.of_nat (2*n) = N.double (N.of_nat n).
Proof. nat2N. Qed.

Lemma inj_succ_double n : N.of_nat (S (2*n)) = N.succ_double (N.of_nat n).
Proof. nat2N. Qed.

Lemma inj_succ n : N.of_nat (S n) = N.succ (N.of_nat n).
Proof. nat2N. Qed.

Lemma inj_pred n : N.of_nat (pred n) = N.pred (N.of_nat n).
Proof. nat2N. Qed.

Lemma inj_add n n' : N.of_nat (n+n') = (N.of_nat n + N.of_nat n')%N.
Proof. nat2N. Qed.

Lemma inj_sub n n' : N.of_nat (n-n') = (N.of_nat n - N.of_nat n')%N.
Proof. nat2N. Qed.

Lemma inj_mul n n' : N.of_nat (n*n') = (N.of_nat n * N.of_nat n')%N.
Proof. nat2N. Qed.

Lemma inj_div2 n : N.of_nat (div2 n) = N.div2 (N.of_nat n).
Proof. nat2N. Qed.

Lemma inj_compare n n' :
  nat_compare n n' = (N.of_nat n ?= N.of_nat n')%N.
Proof. now rewrite N2Nat.inj_compare, !id. Qed.

Lemma inj_min n n' :
  N.of_nat (min n n') = N.min (N.of_nat n) (N.of_nat n').
Proof. nat2N. Qed.

Lemma inj_max n n' :
  N.of_nat (max n n') = N.max (N.of_nat n) (N.of_nat n').
Proof. nat2N. Qed.

Lemma inj_iter n {A} (f:A->A) (x:A) :
  nat_iter n f x = N.iter (N.of_nat n) f x.
Proof. now rewrite N2Nat.inj_iter, !id. Qed.

End Nat2N.

Hint Rewrite Nat2N.id : Nnat.

(** Compatibility notations *)

Notation nat_of_N_inj := N2Nat.inj (only parsing).
Notation N_of_nat_of_N := N2Nat.id (only parsing).
Notation nat_of_Ndouble := N2Nat.inj_double (only parsing).
Notation nat_of_Ndouble_plus_one := N2Nat.inj_succ_double (only parsing).
Notation nat_of_Nsucc := N2Nat.inj_succ (only parsing).
Notation nat_of_Nplus := N2Nat.inj_add (only parsing).
Notation nat_of_Nmult := N2Nat.inj_mul (only parsing).
Notation nat_of_Nminus := N2Nat.inj_sub (only parsing).
Notation nat_of_Npred := N2Nat.inj_pred (only parsing).
Notation nat_of_Ndiv2 := N2Nat.inj_div2 (only parsing).
Notation nat_of_Ncompare := N2Nat.inj_compare (only parsing).
Notation nat_of_Nmax := N2Nat.inj_max (only parsing).
Notation nat_of_Nmin := N2Nat.inj_min (only parsing).

Notation nat_of_N_of_nat := Nat2N.id (only parsing).
Notation N_of_nat_inj := Nat2N.inj (only parsing).
Notation N_of_double := Nat2N.inj_double (only parsing).
Notation N_of_double_plus_one := Nat2N.inj_succ_double (only parsing).
Notation N_of_S := Nat2N.inj_succ (only parsing).
Notation N_of_pred := Nat2N.inj_pred (only parsing).
Notation N_of_plus := Nat2N.inj_add (only parsing).
Notation N_of_minus := Nat2N.inj_sub (only parsing).
Notation N_of_mult := Nat2N.inj_mul (only parsing).
Notation N_of_div2 := Nat2N.inj_div2 (only parsing).
Notation N_of_nat_compare := Nat2N.inj_compare (only parsing).
Notation N_of_min := Nat2N.inj_min (only parsing).
Notation N_of_max := Nat2N.inj_max (only parsing).
