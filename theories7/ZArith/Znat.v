(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Binary Integers (Pierre Crégut, CNET, Lannion, France) *)

Require Export Arith.
Require BinPos.
Require BinInt.
Require Zcompare.
Require Zorder.
Require Decidable.
Require Peano_dec.
Require Export Compare_dec.

Open Local Scope Z_scope.

Definition neq := [x,y:nat] ~(x=y).

(**********************************************************************)
(** Properties of the injection from nat into Z *)

Theorem inj_S : (y:nat) (inject_nat (S y)) = (Zs (inject_nat y)).
Proof.
Intro y; NewInduction y as [|n H]; [
  Unfold Zs ; Simpl; Trivial with arith
| Change (POS (add_un (anti_convert n)))=(Zs (inject_nat (S n)));
  Rewrite add_un_Zs; Trivial with arith].
Qed.
 
Theorem inj_plus : 
  (x,y:nat) (inject_nat (plus x y)) = (Zplus (inject_nat x) (inject_nat y)).
Proof.
Intro x; NewInduction x as [|n H]; Intro y; NewDestruct y as [|m]; [
  Simpl; Trivial with arith
| Simpl; Trivial with arith
| Simpl; Rewrite <- plus_n_O; Trivial with arith
| Change (inject_nat (S (plus n (S m))))=
                        (Zplus (inject_nat (S n)) (inject_nat (S m)));
  Rewrite inj_S; Rewrite H; Do 2 Rewrite inj_S; Rewrite Zplus_S_n; Trivial with arith].
Qed.
 
Theorem inj_mult : 
  (x,y:nat) (inject_nat (mult x y)) = (Zmult (inject_nat x) (inject_nat y)).
Proof.
Intro x; NewInduction x as [|n H]; [
  Simpl; Trivial with arith
| Intro y; Rewrite -> inj_S; Rewrite <- Zmult_Sm_n;
    Rewrite <- H;Rewrite <- inj_plus; Simpl; Rewrite plus_sym; Trivial with arith].
Qed.

Theorem inj_neq:
  (x,y:nat) (neq x y) -> (Zne (inject_nat x) (inject_nat y)).
Proof.
Unfold neq Zne not ; Intros x y H1 H2; Apply H1; Generalize H2; 
Case x; Case y; Intros; [
  Auto with arith
| Discriminate H0
| Discriminate H0
| Simpl in H0; Injection H0; Do 2 Rewrite <- bij1; Intros E; Rewrite E; Auto with arith].
Qed. 

Theorem inj_le:
  (x,y:nat) (le x y) -> (Zle (inject_nat x) (inject_nat y)).
Proof.
Intros x y; Intros H; Elim H; [
  Unfold Zle ; Elim (Zcompare_EGAL (inject_nat x) (inject_nat x));
  Intros H1 H2; Rewrite H2; [ Discriminate | Trivial with arith]
| Intros m H1 H2; Apply Zle_trans with (inject_nat m); 
    [Assumption | Rewrite inj_S; Apply Zle_n_Sn]].
Qed.

Theorem inj_lt: (x,y:nat) (lt x y) -> (Zlt (inject_nat x) (inject_nat y)).
Proof.
Intros x y H; Apply Zgt_lt; Apply Zle_S_gt; Rewrite <- inj_S; Apply inj_le;
Exact H.
Qed.

Theorem inj_gt: (x,y:nat) (gt x y) -> (Zgt (inject_nat x) (inject_nat y)).
Proof.
Intros x y H; Apply Zlt_gt; Apply inj_lt; Exact H.
Qed.

Theorem inj_ge: (x,y:nat) (ge x y) -> (Zge (inject_nat x) (inject_nat y)).
Proof.
Intros x y H; Apply Zle_ge; Apply inj_le; Apply H.
Qed.

Theorem inj_eq: (x,y:nat) x=y -> (inject_nat x) = (inject_nat y).
Proof.
Intros x y H; Rewrite H; Trivial with arith.
Qed.

Theorem intro_Z : 
  (x:nat) (EX y:Z | (inject_nat x)=y /\ 
      	  (Zle ZERO (Zplus (Zmult y (POS xH)) ZERO))).
Proof.
Intros x; Exists (inject_nat x); Split; [
  Trivial with arith
| Rewrite Zmult_sym; Rewrite Zmult_one; Rewrite Zero_right; 
  Unfold Zle ; Elim x; Intros;Simpl; Discriminate ].
Qed.

Theorem inj_minus1 :
  (x,y:nat) (le y x) -> 
    (inject_nat (minus x y)) = (Zminus (inject_nat x) (inject_nat y)).
Proof.
Intros x y H; Apply (Zsimpl_plus_l (inject_nat y)); Unfold Zminus ;
Rewrite Zplus_permute; Rewrite Zplus_inverse_r; Rewrite <- inj_plus;
Rewrite <- (le_plus_minus y x H);Rewrite Zero_right; Trivial with arith.
Qed.
 
Theorem inj_minus2: (x,y:nat) (gt y x) -> (inject_nat (minus x y)) = ZERO.
Proof.
Intros x y H; Rewrite inj_minus_aux; [ Trivial with arith | Apply gt_not_le; Assumption].
Qed.

V7only [ (* From Zdivides *) ].
Theorem POS_inject: (x : positive) (POS x) = (inject_nat (convert x)).
Proof.
Intros x; Elim x; Simpl; Auto.
Intros p H; Rewrite ZL6.
Apply f_equal with f := POS.
Apply convert_intro.
Rewrite bij1; Unfold convert; Simpl.
Rewrite ZL6; Auto.
Intros p H; Unfold convert; Simpl.
Rewrite ZL6; Simpl.
Rewrite inj_plus; Repeat Rewrite <- H.
Rewrite POS_xO; Simpl; Rewrite add_x_x; Reflexivity.
Qed.

