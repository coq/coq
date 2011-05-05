(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Bitwise operations for ZArith *)

Require Import Bool BinPos BinNat BinInt Znat Zeven Zpow_def
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
                 | Zpos a => Pos.testbit a (Npos p)
                 | Zneg a => negb (N.testbit (Pos.pred_N a) (Npos p))
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
   | Zpos a, Zpos b => Zpos (Pos.lor a b)
   | Zneg a, Zpos b => Zneg (N.succ_pos (N.ldiff (Pos.pred_N a) (Npos b)))
   | Zpos a, Zneg b => Zneg (N.succ_pos (N.ldiff (Pos.pred_N b) (Npos a)))
   | Zneg a, Zneg b => Zneg (N.succ_pos (N.land (Pos.pred_N a) (Pos.pred_N b)))
 end.

Definition Zand a b :=
 match a, b with
   | 0, _ => 0
   | _, 0 => 0
   | Zpos a, Zpos b => Z_of_N (Pos.land a b)
   | Zneg a, Zpos b => Z_of_N (N.ldiff (Npos b) (Pos.pred_N a))
   | Zpos a, Zneg b => Z_of_N (N.ldiff (Npos a) (Pos.pred_N b))
   | Zneg a, Zneg b => Zneg (N.succ_pos (N.lor (Pos.pred_N a) (Pos.pred_N b)))
 end.

Definition Zdiff a b :=
 match a, b with
   | 0, _ => 0
   | _, 0 => a
   | Zpos a, Zpos b => Z_of_N (Pos.ldiff a b)
   | Zneg a, Zpos b => Zneg (N.succ_pos (N.lor (Pos.pred_N a) (Npos b)))
   | Zpos a, Zneg b => Z_of_N (N.land (Npos a) (Pos.pred_N b))
   | Zneg a, Zneg b => Z_of_N (N.ldiff (Pos.pred_N b) (Pos.pred_N a))
 end.

Definition Zxor a b :=
 match a, b with
   | 0, _ => b
   | _, 0 => a
   | Zpos a, Zpos b => Z_of_N (Pos.lxor a b)
   | Zneg a, Zpos b => Zneg (N.succ_pos (N.lxor (Pos.pred_N a) (Npos b)))
   | Zpos a, Zneg b => Zneg (N.succ_pos (N.lxor (Npos a) (Pos.pred_N b)))
   | Zneg a, Zneg b => Z_of_N (N.lxor (Pos.pred_N a) (Pos.pred_N b))
 end.


(** Conversions between [Ztestbit] and [Ntestbit] *)

Lemma Ztestbit_of_N : forall a n,
 Ztestbit (Z_of_N a) (Z_of_N n) = N.testbit a n.
Proof.
 intros [ |a] [ |n]; simpl; trivial. now destruct a.
Qed.

Lemma Ztestbit_of_N' : forall a n, 0<=n ->
 Ztestbit (Z_of_N a) n = N.testbit a (Zabs_N n).
Proof.
 intros. now rewrite <- Ztestbit_of_N, Z_of_N_abs, Zabs_eq.
Qed.

Lemma Ztestbit_Zpos : forall a n, 0<=n ->
 Ztestbit (Zpos a) n = N.testbit (Npos a) (Zabs_N n).
Proof.
 intros. now rewrite <- Ztestbit_of_N'.
Qed.

Lemma Ztestbit_Zneg : forall a n, 0<=n ->
 Ztestbit (Zneg a) n = negb (N.testbit (Pos.pred_N a) (Zabs_N n)).
Proof.
 intros a n Hn.
 rewrite <- Ztestbit_of_N' by trivial.
 destruct n as [ |n|n];
  [ | simpl; now destruct (Ppred_N a) | now destruct Hn].
 unfold Ztestbit.
 replace (Z_of_N (Pos.pred_N a)) with (Zpred (Zpos a))
  by (destruct a; trivial).
 now rewrite Zodd_bool_pred, <- Zodd_even_bool.
Qed.

(** Proofs of specifications *)

Lemma Zdiv2_spec : forall a, Zdiv2 a = Zshiftr a 1.
Proof.
 reflexivity.
Qed.

Lemma Ztestbit_0_l : forall n, Ztestbit 0 n = false.
Proof.
 now destruct n.
Qed.

Lemma Ztestbit_neg_r : forall a n, n<0 -> Ztestbit a n = false.
Proof.
 now destruct n.
Qed.

Lemma Ztestbit_odd_0 a : Ztestbit (2*a+1) 0 = true.
Proof.
 now destruct a as [|a|[a|a|]].
Qed.

Lemma Ztestbit_even_0 a : Ztestbit (2*a) 0 = false.
Proof.
 now destruct a.
Qed.

Lemma Ztestbit_odd_succ a n : 0<=n ->
 Ztestbit (2*a+1) (Zsucc n) = Ztestbit a n.
Proof.
 destruct n as [|n|n]; (now destruct 1) || intros _.
 destruct a as [|[a|a|]|[a|a|]]; simpl; trivial. now destruct a.
 unfold Ztestbit. rewrite <- Zpos_succ_morphism.
 destruct a as [|a|[a|a|]]; simpl; trivial;
  rewrite ?Pos.pred_N_succ; now destruct n.
Qed.

Lemma Ztestbit_even_succ a n : 0<=n ->
 Ztestbit (2*a) (Zsucc n) = Ztestbit a n.
Proof.
 destruct n as [|n|n]; (now destruct 1) || intros _.
 destruct a as [|[a|a|]|[a|a|]]; simpl; trivial. now destruct a.
 unfold Ztestbit. rewrite <- Zpos_succ_morphism.
 destruct a as [|a|[a|a|]]; simpl; trivial;
  rewrite ?Pos.pred_N_succ; now destruct n.
Qed.

Lemma Ppred_div2_up : forall p,
 Pos.pred_N (Pos.div2_up p) = N.div2 (Pos.pred_N p).
Proof.
 intros [p|p| ]; trivial.
 simpl. apply Pos.pred_N_succ.
 destruct p; simpl; trivial.
Qed.

Lemma Z_of_N_div2 : forall n, Z_of_N (N.div2 n) = Zdiv2 (Z_of_N n).
Proof.
 intros [|p]; trivial. now destruct p.
Qed.

Lemma Z_of_N_quot2 : forall n, Z_of_N (N.div2 n) = Zquot2 (Z_of_N n).
Proof.
 intros [|p]; trivial. now destruct p.
Qed.

(** Auxiliary results about right shift on positive numbers *)

Lemma Ppred_Pshiftl_low : forall p n m, (m<n)%N ->
 N.testbit (Pos.pred_N (Pos.shiftl p n)) m = true.
Proof.
 induction n using N.peano_ind.
 now destruct m.
 intros m H. unfold Pos.shiftl.
 destruct n as [|n]; simpl in *.
 destruct m. now destruct p. elim (Pos.nlt_1_r _ H).
 rewrite Pos.iter_succ. simpl.
 set (u:=Pos.iter n xO p) in *; clearbody u.
 destruct m as [|m]. now destruct u.
 rewrite <- (IHn (Pos.pred_N m)).
 rewrite <- (N.testbit_odd_succ _ (Pos.pred_N m)).
 rewrite N.succ_pos_pred. now destruct u.
 apply N.le_0_l.
 apply N.succ_lt_mono. now rewrite N.succ_pos_pred.
Qed.

Lemma Ppred_Pshiftl_high : forall p n m, (n<=m)%N ->
 N.testbit (Pos.pred_N (Pos.shiftl p n)) m =
 N.testbit (N.shiftl (Pos.pred_N p) n) m.
Proof.
 induction n using N.peano_ind; intros m H.
 unfold N.shiftl. simpl. now destruct (Pos.pred_N p).
 rewrite N.shiftl_succ_r.
 destruct n as [|n].
 destruct m as [|m]. now destruct H. now destruct p.
 destruct m as [|m]. now destruct H.
 rewrite <- (N.succ_pos_pred m).
 rewrite N.double_spec, N.testbit_even_succ by apply N.le_0_l.
 rewrite <- IHn.
 rewrite N.testbit_succ_r_div2 by apply N.le_0_l.
 f_equal. simpl. rewrite Pos.iter_succ.
 now destruct (Pos.iter n xO p).
 apply N.succ_le_mono. now rewrite N.succ_pos_pred.
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
 exact (N.shiftr_spec' (Npos a) (Npos n) (Zabs_N m)).
 now apply Zplus_le_0_compat.
 (* a < 0 *)
 rewrite <- (iter_pos_swap_gen _ _ _ Pdiv2_up) by trivial.
 rewrite 2 Ztestbit_Zneg; trivial. f_equal.
 rewrite Zabs_N_plus; try easy. simpl Zabs_N.
 rewrite (iter_pos_swap_gen _ _ _ _ Ndiv2) by exact Ppred_div2_up.
 exact (N.shiftr_spec' (Ppred_N a) (Npos n) (Zabs_N m)).
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
 exact (N.shiftl_spec_low (Npos a) (Npos n) (Npos m) H).
 (* a < 0 *)
 rewrite <- (iter_pos_swap_gen _ _ _ xO) by trivial.
 rewrite Ztestbit_Zneg by easy.
 now rewrite (Ppred_Pshiftl_low a (Npos n)).
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
 exact (N.shiftl_spec_high' (Npos p) (Npos n) (Npos m) H).
 (* ... a < 0 *)
 rewrite <- (iter_pos_swap_gen _ _ _ xO) by trivial.
 rewrite 2 Ztestbit_Zneg, EQ by easy. f_equal.
 simpl Zabs_N.
 rewrite <- N.shiftl_spec_high by easy.
 now apply (Ppred_Pshiftl_high p (Npos n)).
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
 now rewrite <- N.lor_spec.
 now rewrite N.ldiff_spec, negb_andb, negb_involutive, orb_comm.
 now rewrite N.ldiff_spec, negb_andb, negb_involutive.
 now rewrite N.land_spec, negb_andb.
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
 now rewrite <- N.land_spec.
 now rewrite N.ldiff_spec.
 now rewrite N.ldiff_spec, andb_comm.
 now rewrite N.lor_spec, negb_orb.
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
 now rewrite <- N.ldiff_spec.
 now rewrite N.land_spec, negb_involutive.
 now rewrite N.lor_spec, negb_orb.
 now rewrite N.ldiff_spec, negb_involutive, andb_comm.
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
 now rewrite <- N.lxor_spec.
 now rewrite N.lxor_spec, negb_xorb_r.
 now rewrite N.lxor_spec, negb_xorb_l.
 now rewrite N.lxor_spec, xorb_negb_negb.
Qed.

(** An additionnal proof concerning [Pshiftl_nat], used in BigN *)


Lemma Pshiftl_nat_Zpower : forall n p,
  Zpos (Pos.shiftl_nat p n) = Zpos p * 2 ^ Z_of_nat n.
Proof.
 intros.
 rewrite Zmult_comm.
 induction n. simpl; auto.
 transitivity (2 * (2 ^ Z_of_nat n * Zpos p)).
 rewrite <- IHn. auto.
 rewrite Zmult_assoc.
 rewrite inj_S.
 rewrite <- Zpower_succ_r; auto with zarith.
 apply Zle_0_nat.
Qed.
