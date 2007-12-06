(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Binary Integers (Pierre Crégut, CNET, Lannion, France) *)

Require Export Arith_base.
Require Import BinPos.
Require Import BinInt.
Require Import Zcompare.
Require Import Zorder.
Require Import Decidable.
Require Import Peano_dec.
Require Import Min Max Zmin Zmax.
Require Export Compare_dec.

Open Local Scope Z_scope.

Definition neq (x y:nat) := x <> y.

(************************************************)
(** Properties of the injection from nat into Z *)

(** Injection and successor *)

Theorem inj_S : forall n:nat, Z_of_nat (S n) = Zsucc (Z_of_nat n).
Proof.
  intro y; induction y as [| n H];
    [ unfold Zsucc in |- *; simpl in |- *; trivial with arith
      | change (Zpos (Psucc (P_of_succ_nat n)) = Zsucc (Z_of_nat (S n))) in |- *;
	rewrite Zpos_succ_morphism; trivial with arith ].
Qed.

(** Injection and equality. *)

Theorem inj_eq : forall n m:nat, n = m -> Z_of_nat n = Z_of_nat m.
Proof.
  intros x y H; rewrite H; trivial with arith.
Qed.

Theorem inj_neq : forall n m:nat, neq n m -> Zne (Z_of_nat n) (Z_of_nat m).
Proof.
  unfold neq, Zne, not in |- *; intros x y H1 H2; apply H1; generalize H2;
    case x; case y; intros;
      [ auto with arith
	| discriminate H0
	| discriminate H0
	| simpl in H0; injection H0;
	  do 2 rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ; 
	    intros E; rewrite E; auto with arith ].
Qed. 

Theorem inj_eq_rev : forall n m:nat, Z_of_nat n = Z_of_nat m -> n = m.
Proof.
  intros x y H.
  destruct (eq_nat_dec x y) as [H'|H']; auto.
  elimtype False.
  exact (inj_neq _ _ H' H).
Qed.

Theorem inj_eq_iff : forall n m:nat, n=m <-> Z_of_nat n = Z_of_nat m.
Proof.
 split; [apply inj_eq | apply inj_eq_rev].
Qed.


(** Injection and order relations: *)

(** One way ... *)

Theorem inj_le : forall n m:nat, (n <= m)%nat -> Z_of_nat n <= Z_of_nat m.
Proof.
  intros x y; intros H; elim H;
    [ unfold Zle in |- *; elim (Zcompare_Eq_iff_eq (Z_of_nat x) (Z_of_nat x));
      intros H1 H2; rewrite H2; [ discriminate | trivial with arith ]
      | intros m H1 H2; apply Zle_trans with (Z_of_nat m);
	[ assumption | rewrite inj_S; apply Zle_succ ] ].
Qed.

Theorem inj_lt : forall n m:nat, (n < m)%nat -> Z_of_nat n < Z_of_nat m.
Proof.
  intros x y H; apply Zgt_lt; apply Zlt_succ_gt; rewrite <- inj_S; apply inj_le;
    exact H.
Qed.

Theorem inj_ge : forall n m:nat, (n >= m)%nat -> Z_of_nat n >= Z_of_nat m.
Proof.
  intros x y H; apply Zle_ge; apply inj_le; apply H.
Qed.

Theorem inj_gt : forall n m:nat, (n > m)%nat -> Z_of_nat n > Z_of_nat m.
Proof.
  intros x y H; apply Zlt_gt; apply inj_lt; exact H.
Qed.

(** The other way ... *)

Theorem inj_le_rev : forall n m:nat, Z_of_nat n <= Z_of_nat m -> (n <= m)%nat.
Proof.
  intros x y H.
  destruct (le_lt_dec x y) as [H0|H0]; auto.
  elimtype False.
  assert (H1:=inj_lt _ _ H0).
  red in H; red in H1.
  rewrite <- Zcompare_antisym in H; rewrite H1 in H; auto.
Qed.

Theorem inj_lt_rev : forall n m:nat, Z_of_nat n < Z_of_nat m -> (n < m)%nat.
Proof.
  intros x y H.
  destruct (le_lt_dec y x) as [H0|H0]; auto.
  elimtype False.
  assert (H1:=inj_le _ _ H0).
  red in H; red in H1.
  rewrite <- Zcompare_antisym in H1; rewrite H in H1; auto.
Qed.

Theorem inj_ge_rev : forall n m:nat, Z_of_nat n >= Z_of_nat m -> (n >= m)%nat.
Proof.
  intros x y H.
  destruct (le_lt_dec y x) as [H0|H0]; auto.
  elimtype False.
  assert (H1:=inj_gt _ _ H0).
  red in H; red in H1.
  rewrite <- Zcompare_antisym in H; rewrite H1 in H; auto.
Qed.

Theorem inj_gt_rev : forall n m:nat, Z_of_nat n > Z_of_nat m -> (n > m)%nat.
Proof.
  intros x y H.
  destruct (le_lt_dec x y) as [H0|H0]; auto.
  elimtype False.
  assert (H1:=inj_ge _ _ H0).
  red in H; red in H1.
  rewrite <- Zcompare_antisym in H1; rewrite H in H1; auto.
Qed.

(* Both ways ... *)

Theorem inj_le_iff : forall n m:nat, (n<=m)%nat <-> Z_of_nat n <= Z_of_nat m.
Proof.
 split; [apply inj_le | apply inj_le_rev].
Qed.

Theorem inj_lt_iff : forall n m:nat, (n<m)%nat <-> Z_of_nat n < Z_of_nat m.
Proof.
 split; [apply inj_lt | apply inj_lt_rev].
Qed.

Theorem inj_ge_iff : forall n m:nat, (n>=m)%nat <-> Z_of_nat n >= Z_of_nat m.
Proof.
 split; [apply inj_ge | apply inj_ge_rev].
Qed.

Theorem inj_gt_iff : forall n m:nat, (n>m)%nat <-> Z_of_nat n > Z_of_nat m.
Proof.
 split; [apply inj_gt | apply inj_gt_rev].
Qed.

(** Injection and usual operations *)
 
Theorem inj_plus : forall n m:nat, Z_of_nat (n + m) = Z_of_nat n + Z_of_nat m.
Proof.
  intro x; induction x as [| n H]; intro y; destruct y as [| m];
    [ simpl in |- *; trivial with arith
      | simpl in |- *; trivial with arith
      | simpl in |- *; rewrite <- plus_n_O; trivial with arith
      | change (Z_of_nat (S (n + S m)) = Z_of_nat (S n) + Z_of_nat (S m)) in |- *;
	rewrite inj_S; rewrite H; do 2 rewrite inj_S; rewrite Zplus_succ_l;
	  trivial with arith ].
Qed.

Theorem inj_mult : forall n m:nat, Z_of_nat (n * m) = Z_of_nat n * Z_of_nat m.
Proof.
  intro x; induction x as [| n H];
    [ simpl in |- *; trivial with arith
      | intro y; rewrite inj_S; rewrite <- Zmult_succ_l_reverse; rewrite <- H;
	rewrite <- inj_plus; simpl in |- *; rewrite plus_comm; 
	  trivial with arith ].
Qed.

Theorem inj_minus1 :
  forall n m:nat, (m <= n)%nat -> Z_of_nat (n - m) = Z_of_nat n - Z_of_nat m.
Proof.
  intros x y H; apply (Zplus_reg_l (Z_of_nat y)); unfold Zminus in |- *;
    rewrite Zplus_permute; rewrite Zplus_opp_r; rewrite <- inj_plus;
      rewrite <- (le_plus_minus y x H); rewrite Zplus_0_r; 
        trivial with arith.
Qed.
 
Theorem inj_minus2 : forall n m:nat, (m > n)%nat -> Z_of_nat (n - m) = 0.
Proof.
  intros x y H; rewrite not_le_minus_0;
    [ trivial with arith | apply gt_not_le; assumption ].
Qed.

Theorem inj_minus : forall n m:nat, 
 Z_of_nat (minus n m) = Zmax 0 (Z_of_nat n - Z_of_nat m).
Proof.
 intros.
 rewrite Zmax_comm.
 unfold Zmax.
 destruct (le_lt_dec m n) as [H|H].

 rewrite (inj_minus1 _ _ H).
 assert (H':=Zle_minus_le_0 _ _ (inj_le _ _ H)).
 unfold Zle in H'.
 rewrite <- Zcompare_antisym in H'.
 destruct Zcompare; simpl in *; intuition.

 rewrite (inj_minus2 _ _ H).
 assert (H':=Zplus_lt_compat_r _ _ (- Z_of_nat m) (inj_lt _ _ H)).
 rewrite Zplus_opp_r in H'.
 unfold Zminus; rewrite H'; auto.
Qed.

Theorem inj_min : forall n m:nat, 
  Z_of_nat (min n m) = Zmin (Z_of_nat n) (Z_of_nat m).
Proof.
 induction n; destruct m; try (compute; auto; fail).
 simpl min.
 do 3 rewrite inj_S.
 rewrite <- Zsucc_min_distr; f_equal; auto.
Qed.

Theorem inj_max : forall n m:nat, 
  Z_of_nat (max n m) = Zmax (Z_of_nat n) (Z_of_nat m).
Proof.
 induction n; destruct m; try (compute; auto; fail).
 simpl max.
 do 3 rewrite inj_S.
 rewrite <- Zsucc_max_distr; f_equal; auto.
Qed.

(** Composition of injections **)

Theorem Zpos_eq_Z_of_nat_o_nat_of_P :
  forall p:positive, Zpos p = Z_of_nat (nat_of_P p).
Proof.
  intros x; elim x; simpl in |- *; auto.
  intros p H; rewrite ZL6.
  apply f_equal with (f := Zpos).
  apply nat_of_P_inj.
  rewrite nat_of_P_o_P_of_succ_nat_eq_succ; unfold nat_of_P in |- *;
    simpl in |- *.
  rewrite ZL6; auto.
  intros p H; unfold nat_of_P in |- *; simpl in |- *.
  rewrite ZL6; simpl in |- *.
  rewrite inj_plus; repeat rewrite <- H.
  rewrite Zpos_xO; simpl in |- *; rewrite Pplus_diag; reflexivity.
Qed.

(** Misc *)

Theorem intro_Z :
  forall n:nat,  exists y : Z, Z_of_nat n = y /\ 0 <= y * 1 + 0.
Proof.
  intros x; exists (Z_of_nat x); split;
    [ trivial with arith
      | rewrite Zmult_comm; rewrite Zmult_1_l; rewrite Zplus_0_r;
	unfold Zle in |- *; elim x; intros; simpl in |- *; 
          discriminate ].
Qed.

Lemma Zpos_P_of_succ_nat : forall n:nat, 
 Zpos (P_of_succ_nat n) = Zsucc (Z_of_nat n).
Proof.
  intros.
  unfold Z_of_nat.
  destruct n.
  simpl; auto.
  simpl (P_of_succ_nat (S n)).
  apply Zpos_succ_morphism.
Qed.
