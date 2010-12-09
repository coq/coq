(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Bitwise operations for ZArith *)

Require Import Bool BinPos BinNat BinInt Ndigits Znat Zeven Zpow_def
 Zorder Zcompare.

Local Open Scope Z_scope.

(** When accessing the bits of negative numbers, all functions
  below will use the two's complement representation. For instance,
  [-1] will correspond to an infinite stream of true bits. If this
  isn't what you're looking for, you can use [Zabs] first and then
  access the bits of the absolute value.
*)

(** [Ztestbit] : accessing the [n]-th bit of a number [a].
    For negative [n], we arbitrarily answer [false]. *)

Definition Ztestbit a n :=
 match n with
   | 0 => Zodd_bool a
   | Zpos p => match a with
                 | 0 => false
                 | Zpos a => Ptestbit a (Npos p)
                 | Zneg a => negb (Ntestbit (Ppred_N a) (Npos p))
               end
   | Zneg _ => false
 end.

(** Shifts

   Nota: a shift to the right by [-n] will be a shift to the left
   by [n], and vice-versa.

   For fulfilling the two's complement convention, shifting to
   the right a negative number should correspond to a division
   by 2 with rounding toward bottom, hence the use of [Zdiv2]
   instead of [Zquot2].
*)

Definition Zshiftl a n :=
 match n with
   | 0 => a
   | Zpos p => iter_pos p _ (Zmult 2) a
   | Zneg p => iter_pos p _ Zdiv2 a
 end.

Definition Zshiftr a n := Zshiftl a (-n).

(** Bitwise operations Zor Zand Zdiff Zxor *)

Definition Zor a b :=
 match a, b with
   | 0, _ => b
   | _, 0 => a
   | Zpos a, Zpos b => Zpos (Por a b)
   | Zneg a, Zpos b => Zneg (Nsucc_pos (Ndiff (Ppred_N a) (Npos b)))
   | Zpos a, Zneg b => Zneg (Nsucc_pos (Ndiff (Ppred_N b) (Npos a)))
   | Zneg a, Zneg b => Zneg (Nsucc_pos (Nand (Ppred_N a) (Ppred_N b)))
 end.

Definition Zand a b :=
 match a, b with
   | 0, _ => 0
   | _, 0 => 0
   | Zpos a, Zpos b => Z_of_N (Pand a b)
   | Zneg a, Zpos b => Z_of_N (Ndiff (Npos b) (Ppred_N a))
   | Zpos a, Zneg b => Z_of_N (Ndiff (Npos a) (Ppred_N b))
   | Zneg a, Zneg b => Zneg (Nsucc_pos (Nor (Ppred_N a) (Ppred_N b)))
 end.

Definition Zdiff a b :=
 match a, b with
   | 0, _ => 0
   | _, 0 => a
   | Zpos a, Zpos b => Z_of_N (Pdiff a b)
   | Zneg a, Zpos b => Zneg (Nsucc_pos (Nor (Ppred_N a) (Npos b)))
   | Zpos a, Zneg b => Z_of_N (Nand (Npos a) (Ppred_N b))
   | Zneg a, Zneg b => Z_of_N (Ndiff (Ppred_N b) (Ppred_N a))
 end.

Definition Zxor a b :=
 match a, b with
   | 0, _ => b
   | _, 0 => a
   | Zpos a, Zpos b => Z_of_N (Pxor a b)
   | Zneg a, Zpos b => Zneg (Nsucc_pos (Nxor (Ppred_N a) (Npos b)))
   | Zpos a, Zneg b => Zneg (Nsucc_pos (Nxor (Npos a) (Ppred_N b)))
   | Zneg a, Zneg b => Z_of_N (Nxor (Ppred_N a) (Ppred_N b))
 end.

(** Proofs of specifications *)

Lemma Zdiv2_spec : forall a, Zdiv2 a = Zshiftr a 1.
Proof.
 reflexivity.
Qed.

Lemma Ztestbit_neg_r : forall a n, n<0 -> Ztestbit a n = false.
Proof.
 now destruct n.
Qed.

Lemma Ztestbit_spec : forall a n, 0<=n ->
  exists l, exists h, 0<=l<2^n /\
    a = l + ((if Ztestbit a n then 1 else 0) + 2*h)*2^n.
Proof.
 intros a [ |n|n] Hn; (now destruct Hn) || clear Hn.
 (* n = 0 *)
 simpl Ztestbit.
 exists 0. exists (Zdiv2 a). repeat split. easy.
 now rewrite Zplus_0_l, Zmult_1_r, Zplus_comm, <- Zdiv2_odd_eqn.
 (* n > 0 *)
 destruct a.
 (* ... a = 0 *)
 exists 0. exists 0. repeat split; try easy. now rewrite Zpower_Ppow.
 (* ... a > 0 *)
 simpl Ztestbit.
 destruct (Ntestbit_spec (Npos p) (Npos n)) as (l & h & (_,Hl) & EQ).
 exists (Z_of_N l). exists (Z_of_N h).
 simpl Npow in *; simpl Ntestbit in *. rewrite Zpower_Ppow.
 repeat split.
 apply Z_of_N_le_0.
 rewrite <-Z_of_N_pos. now apply Z_of_N_lt.
 rewrite <-Z_of_N_pos, EQ.
 rewrite Z_of_N_plus, Z_of_N_mult. f_equal. f_equal.
 destruct Ptestbit; now rewrite Z_of_N_plus, Z_of_N_mult.
 (* ... a < 0 *)
 simpl Ztestbit.
 destruct (Ntestbit_spec (Ppred_N p) (Npos n)) as (l & h & (_,Hl) & EQ).
 exists (2^Zpos n - (Z_of_N l) - 1). exists (-Z_of_N h - 1).
 simpl Npow in *. rewrite Zpower_Ppow.
 repeat split.
 apply Zle_minus_le_0.
 change 1 with (Zsucc 0). apply Zle_succ_l.
 apply Zlt_plus_swap. simpl. rewrite <-Z_of_N_pos. now apply Z_of_N_lt.
 apply Zlt_plus_swap. unfold Zminus. rewrite Zopp_involutive.
 fold (Zsucc (Zpos (2^n))). apply Zlt_succ_r.
 apply Zle_plus_swap. unfold Zminus. rewrite Zopp_involutive.
 rewrite <- (Zplus_0_r (Zpos (2^n))) at 1. apply Zplus_le_compat_l.
 apply Z_of_N_le_0.
 apply Zopp_inj. unfold Zminus.
 rewrite Zopp_neg, !Zopp_plus_distr, !Zopp_involutive.
 rewrite Zopp_mult_distr_l, Zopp_plus_distr, Zopp_mult_distr_r,
  Zopp_plus_distr, !Zopp_involutive.
 rewrite Ppred_N_spec in EQ at 1.
 apply (f_equal Nsucc) in EQ. rewrite Nsucc_pred in EQ by easy.
 rewrite <-Z_of_N_pos, EQ.
 rewrite Z_of_N_succ, Z_of_N_plus, Z_of_N_mult, Z_of_N_pos. unfold Zsucc.
 rewrite <- (Zplus_assoc _ 1), (Zplus_comm 1), Zplus_assoc. f_equal.
 rewrite (Zplus_comm (- _)), <- Zplus_assoc. f_equal.
 change (- Zpos (2^n)) with ((-1)*(Zpos (2^n))). rewrite <- Zmult_plus_distr_l.
 f_equal.
 rewrite Z_of_N_plus, Z_of_N_mult.
 rewrite Zmult_plus_distr_r, Zmult_1_r, (Zplus_comm _ 2), !Zplus_assoc.
 rewrite (Zplus_comm _ 2), Zplus_assoc. change (2+-1) with 1.
 f_equal.
 now destruct Ntestbit.
Qed.

(** Conversions between [Ztestbit] and [Ntestbit] *)

Lemma Ztestbit_of_N : forall a n,
 Ztestbit (Z_of_N a) (Z_of_N n) = Ntestbit a n.
Proof.
 intros [ |a] [ |n]; simpl; trivial. now destruct a.
Qed.

Lemma Ztestbit_of_N' : forall a n, 0<=n ->
 Ztestbit (Z_of_N a) n = Ntestbit a (Zabs_N n).
Proof.
 intros. now rewrite <- Ztestbit_of_N, Z_of_N_abs, Zabs_eq.
Qed.

Lemma Ztestbit_Zpos : forall a n, 0<=n ->
 Ztestbit (Zpos a) n = Ntestbit (Npos a) (Zabs_N n).
Proof.
 intros. now rewrite <- Ztestbit_of_N'.
Qed.

Lemma Ztestbit_Zneg : forall a n, 0<=n ->
 Ztestbit (Zneg a) n = negb (Ntestbit (Ppred_N a) (Zabs_N n)).
Proof.
 intros a n Hn.
 rewrite <- Ztestbit_of_N' by trivial.
 destruct n as [ |n|n];
  [ | simpl; now destruct (Ppred_N a) | now destruct Hn].
 unfold Ztestbit.
 replace (Z_of_N (Ppred_N a)) with (Zpred (Zpos a))
  by (destruct a; trivial).
 now rewrite Zodd_bool_pred, <- Zodd_even_bool.
Qed.

Lemma Ztestbit_0_l : forall n, Ztestbit 0 n = false.
Proof.
 now destruct n.
Qed.

Lemma Ppred_div2_up : forall p,
 Ppred_N (Pdiv2_up p) = Ndiv2 (Ppred_N p).
Proof.
 intros [p|p| ]; trivial.
 simpl. rewrite Ppred_N_spec. apply (Npred_succ (Npos p)).
 destruct p; simpl; trivial.
Qed.

Lemma Z_of_N_div2 : forall n, Z_of_N (Ndiv2 n) = Zdiv2 (Z_of_N n).
Proof.
 intros [|p]; trivial. now destruct p.
Qed.

Lemma Z_of_N_quot2 : forall n, Z_of_N (Ndiv2 n) = Zquot2 (Z_of_N n).
Proof.
 intros [|p]; trivial. now destruct p.
Qed.

(** Auxiliary results about right shift on positive numbers *)

Lemma Ppred_Pshiftl_low : forall p n m, (m<n)%nat ->
 Nbit (Ppred_N (iter_nat n _ xO p)) m = true.
Proof.
 induction n.
 inversion 1.
 intros m H. simpl.
 destruct m.
 now destruct (iter_nat n _ xO p).
 apply lt_S_n in H.
 specialize (IHn m H).
 now destruct (iter_nat n _ xO p).
Qed.

Lemma Ppred_Pshiftl_high : forall p n m, (n<=m)%nat ->
 Nbit (Ppred_N (iter_nat n _ xO p)) m =
 Nbit (Nshiftl_nat (Ppred_N p) n) m.
Proof.
 induction n.
 now unfold Nshiftl_nat.
 intros m H.
 destruct m.
 inversion H.
 apply le_S_n in H.
 rewrite Nshiftl_nat_S.
 specialize (IHn m H).
 simpl in *.
 unfold Nbit.
 now destruct (Nshiftl_nat (Ppred_N p) n), (iter_nat n positive xO p).
Qed.

(** Correctness proofs about [Zshiftr] and [Zshiftl] *)

Lemma Zshiftr_spec_aux : forall a n m, 0<=n -> 0<=m ->
 Ztestbit (Zshiftr a n) m = Ztestbit a (m+n).
Proof.
 intros a n m Hn Hm. unfold Zshiftr.
 destruct n as [ |n|n]; (now destruct Hn) || clear Hn; simpl.
 now rewrite Zplus_0_r.
 destruct a as [ |a|a].
 (* a = 0 *)
 replace (iter_pos n _ Zdiv2 0) with 0
  by (apply iter_pos_invariant; intros; subst; trivial).
 now rewrite 2 Ztestbit_0_l.
 (* a > 0 *)
 rewrite <- (Z_of_N_pos a) at 1.
 rewrite <- (iter_pos_swap_gen _ _ _ Ndiv2) by exact Z_of_N_div2.
 rewrite Ztestbit_Zpos, Ztestbit_of_N'; trivial.
 rewrite Zabs_N_plus; try easy. simpl Zabs_N.
 exact (Nshiftr_spec (Npos a) (Npos n) (Zabs_N m)).
 now apply Zplus_le_0_compat.
 (* a < 0 *)
 rewrite <- (iter_pos_swap_gen _ _ _ Pdiv2_up) by trivial.
 rewrite 2 Ztestbit_Zneg; trivial. f_equal.
 rewrite Zabs_N_plus; try easy. simpl Zabs_N.
 rewrite (iter_pos_swap_gen _ _ _ _ Ndiv2) by exact Ppred_div2_up.
 exact (Nshiftr_spec (Ppred_N a) (Npos n) (Zabs_N m)).
 now apply Zplus_le_0_compat.
Qed.

Lemma Zshiftl_spec_low : forall a n m, m<n ->
 Ztestbit (Zshiftl a n) m = false.
Proof.
 intros a [ |n|n] [ |m|m] H; try easy; simpl Zshiftl.
 rewrite iter_nat_of_P.
 destruct (nat_of_P_is_S n) as (n' & ->).
 simpl. now destruct (iter_nat n' _  (Zmult 2) a).
 destruct a as [ |a|a].
 (* a = 0 *)
 replace (iter_pos n _ (Zmult 2) 0) with 0
  by (apply iter_pos_invariant; intros; subst; trivial).
 apply Ztestbit_0_l.
 (* a > 0 *)
 rewrite <- (iter_pos_swap_gen _ _ _ xO) by trivial.
 rewrite Ztestbit_Zpos by easy.
 exact (Nshiftl_spec_low (Npos a) (Npos n) (Npos m) H).
 (* a < 0 *)
 rewrite <- (iter_pos_swap_gen _ _ _ xO) by trivial.
 rewrite Ztestbit_Zneg by easy.
 simpl Zabs_N.
 rewrite <- Nbit_Ntestbit, iter_nat_of_P. simpl nat_of_N.
 rewrite Ppred_Pshiftl_low; trivial.
 now apply Plt_lt.
Qed.

Lemma Zshiftl_spec_high : forall a n m, 0<=m -> n<=m ->
 Ztestbit (Zshiftl a n) m = Ztestbit a (m-n).
Proof.
 intros a n m Hm H.
 destruct n as [ |n|n]. simpl. now rewrite Zminus_0_r.
 (* n > 0 *)
 destruct m as [ |m|m]; try (now destruct H).
 assert (0 <= Zpos m - Zpos n) by (now apply Zle_minus_le_0).
 assert (EQ : Zabs_N (Zpos m - Zpos n) =  (Npos m - Npos n)%N).
  apply Z_of_N_eq_rev. rewrite Z_of_N_abs, Zabs_eq by trivial.
  now rewrite Z_of_N_minus, !Z_of_N_pos, Zmax_r.
 destruct a; unfold Zshiftl.
 (* ... a = 0 *)
 replace (iter_pos n _ (Zmult 2) 0) with 0
  by (apply iter_pos_invariant; intros; subst; trivial).
 now rewrite 2 Ztestbit_0_l.
 (* ... a > 0 *)
 rewrite <- (iter_pos_swap_gen _ _ _ xO) by trivial.
 rewrite 2 Ztestbit_Zpos, EQ by easy.
 exact (Nshiftl_spec_high (Npos p) (Npos n) (Npos m) H).
 (* ... a < 0 *)
 rewrite <- (iter_pos_swap_gen _ _ _ xO) by trivial.
 rewrite 2 Ztestbit_Zneg, EQ by easy. f_equal.
 simpl Zabs_N.
 rewrite <- Nshiftl_spec_high by easy.
 rewrite <- 2 Nbit_Ntestbit, iter_nat_of_P, <- Nshiftl_nat_equiv.
 simpl nat_of_N.
 apply Ppred_Pshiftl_high.
 now apply Ple_le.
 (* n < 0 *)
 unfold Zminus. simpl.
 now apply (Zshiftr_spec_aux a (Zpos n) m).
Qed.

Lemma Zshiftr_spec : forall a n m, 0<=m ->
 Ztestbit (Zshiftr a n) m = Ztestbit a (m+n).
Proof.
 intros a n m Hm.
 destruct (Zle_or_lt 0 n).
 now apply Zshiftr_spec_aux.
 destruct (Zle_or_lt (-n) m).
 unfold Zshiftr.
 rewrite (Zshiftl_spec_high a (-n) m); trivial.
 unfold Zminus. now rewrite Zopp_involutive.
 unfold Zshiftr.
 rewrite (Zshiftl_spec_low a (-n) m); trivial.
 rewrite Ztestbit_neg_r; trivial.
 now apply Zlt_plus_swap.
Qed.

(** Correctness proofs for bitwise operations *)

Lemma Zor_spec : forall a b n,
 Ztestbit (Zor a b) n = Ztestbit a n || Ztestbit b n.
Proof.
 intros a b n.
 destruct (Zle_or_lt 0 n) as [Hn|Hn]; [|now rewrite !Ztestbit_neg_r].
 destruct a as [ |a|a], b as [ |b|b];
  rewrite ?Ztestbit_0_l, ?orb_false_r; trivial; unfold Zor;
  rewrite ?Ztestbit_Zpos, ?Ztestbit_Zneg, ?Ppred_Nsucc
   by trivial.
 now rewrite <- Nor_spec.
 now rewrite Ndiff_spec, negb_andb, negb_involutive, orb_comm.
 now rewrite Ndiff_spec, negb_andb, negb_involutive.
 now rewrite Nand_spec, negb_andb.
Qed.

Lemma Zand_spec : forall a b n,
 Ztestbit (Zand a b) n = Ztestbit a n && Ztestbit b n.
Proof.
 intros a b n.
 destruct (Zle_or_lt 0 n) as [Hn|Hn]; [|now rewrite !Ztestbit_neg_r].
 destruct a as [ |a|a], b as [ |b|b];
  rewrite ?Ztestbit_0_l, ?andb_false_r; trivial; unfold Zand;
  rewrite ?Ztestbit_Zpos, ?Ztestbit_Zneg, ?Ztestbit_of_N', ?Ppred_Nsucc
   by trivial.
 now rewrite <- Nand_spec.
 now rewrite Ndiff_spec.
 now rewrite Ndiff_spec, andb_comm.
 now rewrite Nor_spec, negb_orb.
Qed.

Lemma Zdiff_spec : forall a b n,
 Ztestbit (Zdiff a b) n = Ztestbit a n && negb (Ztestbit b n).
Proof.
 intros a b n.
 destruct (Zle_or_lt 0 n) as [Hn|Hn]; [|now rewrite !Ztestbit_neg_r].
 destruct a as [ |a|a], b as [ |b|b];
  rewrite ?Ztestbit_0_l, ?andb_true_r; trivial; unfold Zdiff;
  rewrite ?Ztestbit_Zpos, ?Ztestbit_Zneg, ?Ztestbit_of_N', ?Ppred_Nsucc
   by trivial.
 now rewrite <- Ndiff_spec.
 now rewrite Nand_spec, negb_involutive.
 now rewrite Nor_spec, negb_orb.
 now rewrite Ndiff_spec, negb_involutive, andb_comm.
Qed.

Lemma Zxor_spec : forall a b n,
 Ztestbit (Zxor a b) n = xorb (Ztestbit a n) (Ztestbit b n).
Proof.
 intros a b n.
 destruct (Zle_or_lt 0 n) as [Hn|Hn]; [|now rewrite !Ztestbit_neg_r].
 destruct a as [ |a|a], b as [ |b|b];
  rewrite ?Ztestbit_0_l, ?xorb_false_l, ?xorb_false_r; trivial; unfold Zxor;
  rewrite ?Ztestbit_Zpos, ?Ztestbit_Zneg, ?Ztestbit_of_N', ?Ppred_Nsucc
   by trivial.
 now rewrite <- Nxor_spec.
 now rewrite Nxor_spec, negb_xorb_r.
 now rewrite Nxor_spec, negb_xorb_l.
 now rewrite Nxor_spec, xorb_negb_negb.
Qed.
