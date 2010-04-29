(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Arith_base.
Require Import Compare_dec.
Require Import Sumbool.
Require Import Div2.
Require Import Min.
Require Import Max.
Require Import BinPos.
Require Import BinNat.
Require Import BinInt.
Require Import Pnat.
Require Import Zmax.
Require Import Zmin.
Require Import Znat.

(** Translation from [N] to [nat] and back. *)

Definition nat_of_N (a:N) :=
  match a with
  | N0 => 0%nat
  | Npos p => nat_of_P p
  end.

Definition N_of_nat (n:nat) :=
  match n with
  | O => N0
  | S n' => Npos (P_of_succ_nat n')
  end.

Lemma N_of_nat_of_N : forall a:N, N_of_nat (nat_of_N a) = a.
Proof.
  destruct a as [| p]. reflexivity.
  simpl in |- *. elim (ZL4 p). intros n H. rewrite H. simpl in |- *.
  rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ in H.
  rewrite nat_of_P_inj with (1 := H). reflexivity.
Qed.

Lemma nat_of_N_of_nat : forall n:nat, nat_of_N (N_of_nat n) = n.
Proof.
  induction n. trivial.
  intros. simpl in |- *. apply nat_of_P_o_P_of_succ_nat_eq_succ.
Qed.

(** Interaction of this translation and usual operations. *)

Lemma nat_of_Ndouble : forall a, nat_of_N (Ndouble a) = 2*(nat_of_N a).
Proof.
  destruct a; simpl nat_of_N; auto.
  apply nat_of_P_xO.
Qed.

Lemma N_of_double : forall n, N_of_nat (2*n) = Ndouble (N_of_nat n).
Proof.
  intros.
  pattern n at 1; rewrite <- (nat_of_N_of_nat n).
  rewrite <- nat_of_Ndouble.
  apply N_of_nat_of_N.
Qed.

Lemma nat_of_Ndouble_plus_one :
  forall a, nat_of_N (Ndouble_plus_one a) = S (2*(nat_of_N a)).
Proof.
  destruct a; simpl nat_of_N; auto.
  apply nat_of_P_xI.
Qed.

Lemma N_of_double_plus_one :
  forall n, N_of_nat (S (2*n)) = Ndouble_plus_one (N_of_nat n).
Proof.
  intros.
  pattern n at 1; rewrite <- (nat_of_N_of_nat n).
  rewrite <- nat_of_Ndouble_plus_one.
  apply N_of_nat_of_N.
Qed.

Lemma nat_of_Nsucc : forall a, nat_of_N (Nsucc a) = S (nat_of_N a).
Proof.
  destruct a; simpl.
  apply nat_of_P_xH.
  apply nat_of_P_succ_morphism.
Qed.

Lemma N_of_S : forall n, N_of_nat (S n) = Nsucc (N_of_nat n).
Proof.
  intros.
  pattern n at 1; rewrite <- (nat_of_N_of_nat n).
  rewrite <- nat_of_Nsucc.
  apply N_of_nat_of_N.
Qed.

Lemma nat_of_Nplus :
  forall a a', nat_of_N (Nplus a a') = (nat_of_N a)+(nat_of_N a').
Proof.
  destruct a; destruct a'; simpl; auto.
  apply nat_of_P_plus_morphism.
Qed.

Lemma N_of_plus :
  forall n n', N_of_nat (n+n') = Nplus (N_of_nat n) (N_of_nat n').
Proof.
  intros.
  pattern n at 1; rewrite <- (nat_of_N_of_nat n).
  pattern n' at 1; rewrite <- (nat_of_N_of_nat n').
  rewrite <- nat_of_Nplus.
  apply N_of_nat_of_N.
Qed.

Lemma nat_of_Nminus :
  forall a a', nat_of_N (Nminus a a') = ((nat_of_N a)-(nat_of_N a'))%nat.
Proof.
  destruct a; destruct a'; simpl; auto with arith.
  case_eq (Pcompare p p0 Eq); simpl; intros.
  rewrite (Pcompare_Eq_eq _ _ H); auto with arith.
  rewrite Pminus_mask_diag. simpl. apply minus_n_n.
  rewrite Pminus_mask_Lt. pose proof (nat_of_P_lt_Lt_compare_morphism _ _ H). simpl.
  symmetry; apply not_le_minus_0. auto with arith. assumption.
  pose proof (Pminus_mask_Gt p p0 H) as H1. destruct H1 as [q [H1 _]]. rewrite H1; simpl.
  replace q with (Pminus p p0) by (unfold Pminus; now rewrite H1).
  apply nat_of_P_minus_morphism; auto.
Qed.

Lemma N_of_minus :
  forall n n', N_of_nat (n-n') = Nminus (N_of_nat n) (N_of_nat n').
Proof.
  intros.
  pattern n at 1; rewrite <- (nat_of_N_of_nat n).
  pattern n' at 1; rewrite <- (nat_of_N_of_nat n').
  rewrite <- nat_of_Nminus.
  apply N_of_nat_of_N.
Qed.

Lemma nat_of_Nmult :
  forall a a', nat_of_N (Nmult a a') = (nat_of_N a)*(nat_of_N a').
Proof.
  destruct a; destruct a'; simpl; auto.
  apply nat_of_P_mult_morphism.
Qed.

Lemma N_of_mult :
  forall n n', N_of_nat (n*n') = Nmult (N_of_nat n) (N_of_nat n').
Proof.
  intros.
  pattern n at 1; rewrite <- (nat_of_N_of_nat n).
  pattern n' at 1; rewrite <- (nat_of_N_of_nat n').
  rewrite <- nat_of_Nmult.
  apply N_of_nat_of_N.
Qed.

Lemma nat_of_Ndiv2 :
  forall a, nat_of_N (Ndiv2 a) = div2 (nat_of_N a).
Proof.
  destruct a; simpl in *; auto.
  destruct p; auto.
  rewrite nat_of_P_xI.
  rewrite div2_double_plus_one; auto.
  rewrite nat_of_P_xO.
  rewrite div2_double; auto.
Qed.

Lemma N_of_div2 :
  forall n, N_of_nat (div2 n) = Ndiv2 (N_of_nat n).
Proof.
  intros.
  pattern n at 1; rewrite <- (nat_of_N_of_nat n).
  rewrite <- nat_of_Ndiv2.
  apply N_of_nat_of_N.
Qed.

Lemma nat_of_Ncompare :
 forall a a', Ncompare a a' = nat_compare (nat_of_N a) (nat_of_N a').
Proof.
  destruct a; destruct a'; simpl.
  reflexivity.
  assert (NZ : 0 < nat_of_P p) by auto using lt_O_nat_of_P.
  destruct nat_of_P; [inversion NZ|auto].
  assert (NZ : 0 < nat_of_P p) by auto using lt_O_nat_of_P.
  destruct nat_of_P; [inversion NZ|auto].
  apply nat_of_P_compare_morphism.
Qed.

Lemma N_of_nat_compare :
 forall n n', nat_compare n n' = Ncompare (N_of_nat n) (N_of_nat n').
Proof.
  intros.
  pattern n at 1; rewrite <- (nat_of_N_of_nat n).
  pattern n' at 1; rewrite <- (nat_of_N_of_nat n').
  symmetry; apply nat_of_Ncompare.
Qed.

Lemma nat_of_Nmin :
  forall a a', nat_of_N (Nmin a a') = min (nat_of_N a) (nat_of_N a').
Proof.
  intros; unfold Nmin; rewrite nat_of_Ncompare.
  rewrite nat_compare_equiv; unfold nat_compare_alt.
  destruct (lt_eq_lt_dec (nat_of_N a) (nat_of_N a')) as [[|]|];
    simpl; intros; symmetry; auto with arith.
  apply min_l; rewrite e; auto with arith.
Qed.

Lemma N_of_min :
  forall n n', N_of_nat (min n n') = Nmin (N_of_nat n) (N_of_nat n').
Proof.
  intros.
  pattern n at 1; rewrite <- (nat_of_N_of_nat n).
  pattern n' at 1; rewrite <- (nat_of_N_of_nat n').
  rewrite <- nat_of_Nmin.
  apply N_of_nat_of_N.
Qed.

Lemma nat_of_Nmax :
  forall a a', nat_of_N (Nmax a a') = max (nat_of_N a) (nat_of_N a').
Proof.
  intros; unfold Nmax; rewrite nat_of_Ncompare.
  rewrite nat_compare_equiv; unfold nat_compare_alt.
  destruct (lt_eq_lt_dec (nat_of_N a) (nat_of_N a')) as [[|]|];
    simpl; intros; symmetry; auto with arith.
  apply max_r; rewrite e; auto with arith.
Qed.

Lemma N_of_max :
  forall n n', N_of_nat (max n n') = Nmax (N_of_nat n) (N_of_nat n').
Proof.
  intros.
  pattern n at 1; rewrite <- (nat_of_N_of_nat n).
  pattern n' at 1; rewrite <- (nat_of_N_of_nat n').
  rewrite <- nat_of_Nmax.
  apply N_of_nat_of_N.
Qed.

(** Properties concerning [Z_of_N] *)

Lemma Z_of_nat_of_N : forall n:N, Z_of_nat (nat_of_N n) = Z_of_N n.
Proof.
  destruct n; simpl; auto; symmetry; apply Zpos_eq_Z_of_nat_o_nat_of_P.
Qed.

Lemma Z_of_N_eq : forall n m, n = m -> Z_of_N n = Z_of_N m.
Proof.
 intros; f_equal; assumption.
Qed.

Lemma Z_of_N_eq_rev : forall n m, Z_of_N n = Z_of_N m -> n = m.
Proof.
 intros [|n] [|m]; simpl; intros; try discriminate; congruence.
Qed.

Lemma Z_of_N_eq_iff : forall n m, n = m <-> Z_of_N n = Z_of_N m.
Proof.
 split; [apply Z_of_N_eq | apply Z_of_N_eq_rev].
Qed.

Lemma Z_of_N_le : forall n m, (n<=m)%N -> (Z_of_N n <= Z_of_N m)%Z.
Proof.
 intros [|n] [|m]; simpl; auto.
Qed.

Lemma Z_of_N_le_rev : forall n m, (Z_of_N n <= Z_of_N m)%Z -> (n<=m)%N.
Proof.
 intros [|n] [|m]; simpl; auto.
Qed.

Lemma Z_of_N_le_iff : forall n m, (n<=m)%N <-> (Z_of_N n <= Z_of_N m)%Z.
Proof.
 split; [apply Z_of_N_le | apply Z_of_N_le_rev].
Qed.

Lemma Z_of_N_lt : forall n m, (n<m)%N -> (Z_of_N n < Z_of_N m)%Z.
Proof.
 intros [|n] [|m]; simpl; auto.
Qed.

Lemma Z_of_N_lt_rev : forall n m, (Z_of_N n < Z_of_N m)%Z -> (n<m)%N.
Proof.
 intros [|n] [|m]; simpl; auto.
Qed.

Lemma Z_of_N_lt_iff : forall n m, (n<m)%N <-> (Z_of_N n < Z_of_N m)%Z.
Proof.
 split; [apply Z_of_N_lt | apply Z_of_N_lt_rev].
Qed.

Lemma Z_of_N_ge : forall n m, (n>=m)%N -> (Z_of_N n >= Z_of_N m)%Z.
Proof.
 intros [|n] [|m]; simpl; auto.
Qed.

Lemma Z_of_N_ge_rev : forall n m, (Z_of_N n >= Z_of_N m)%Z -> (n>=m)%N.
Proof.
 intros [|n] [|m]; simpl; auto.
Qed.

Lemma Z_of_N_ge_iff : forall n m, (n>=m)%N <-> (Z_of_N n >= Z_of_N m)%Z.
Proof.
 split; [apply Z_of_N_ge | apply Z_of_N_ge_rev].
Qed.

Lemma Z_of_N_gt : forall n m, (n>m)%N -> (Z_of_N n > Z_of_N m)%Z.
Proof.
 intros [|n] [|m]; simpl; auto.
Qed.

Lemma Z_of_N_gt_rev : forall n m, (Z_of_N n > Z_of_N m)%Z -> (n>m)%N.
Proof.
 intros [|n] [|m]; simpl; auto.
Qed.

Lemma Z_of_N_gt_iff : forall n m, (n>m)%N <-> (Z_of_N n > Z_of_N m)%Z.
Proof.
 split; [apply Z_of_N_gt | apply Z_of_N_gt_rev].
Qed.

Lemma Z_of_N_of_nat : forall n:nat, Z_of_N (N_of_nat n) = Z_of_nat n.
Proof.
 destruct n; simpl; auto.
Qed.

Lemma Z_of_N_pos : forall p:positive, Z_of_N (Npos p) = Zpos p.
Proof.
 destruct p; simpl; auto.
Qed.

Lemma Z_of_N_abs : forall z:Z, Z_of_N (Zabs_N z) = Zabs z.
Proof.
 destruct z; simpl; auto.
Qed.

Lemma Z_of_N_le_0 : forall n, (0 <= Z_of_N n)%Z.
Proof.
 destruct n; intro; discriminate.
Qed.

Lemma Z_of_N_plus : forall n m:N, Z_of_N (n+m) = (Z_of_N n + Z_of_N m)%Z.
Proof.
 destruct n; destruct m; auto.
Qed.

Lemma Z_of_N_mult : forall n m:N, Z_of_N (n*m) = (Z_of_N n * Z_of_N m)%Z.
Proof.
 destruct n; destruct m; auto.
Qed.

Lemma Z_of_N_minus : forall n m:N, Z_of_N (n-m) = Zmax 0 (Z_of_N n - Z_of_N m).
Proof.
 intros; do 3 rewrite <- Z_of_nat_of_N; rewrite nat_of_Nminus; apply inj_minus.
Qed.

Lemma Z_of_N_succ : forall n:N, Z_of_N (Nsucc n) = Zsucc (Z_of_N n).
Proof.
 intros; do 2 rewrite <- Z_of_nat_of_N; rewrite nat_of_Nsucc; apply inj_S.
Qed.

Lemma Z_of_N_min : forall n m:N, Z_of_N (Nmin n m) = Zmin (Z_of_N n) (Z_of_N m).
Proof.
 intros; do 3 rewrite <- Z_of_nat_of_N; rewrite nat_of_Nmin; apply inj_min.
Qed.

Lemma Z_of_N_max : forall n m:N, Z_of_N (Nmax n m) = Zmax (Z_of_N n) (Z_of_N m).
Proof.
 intros; do 3 rewrite <- Z_of_nat_of_N; rewrite nat_of_Nmax; apply inj_max.
Qed.

