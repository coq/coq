(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(** Binary Integers (Pierre Crégut, CNET, Lannion, France) *)

Require Export Arith.
Require fast_integer.
Require Zorder.
Require zarith_aux.
Require Decidable.
Require Peano_dec.
Require Export Compare_dec.

Open Local Scope Z_scope.

Definition neq := [x,y:nat] ~(x=y).

(**********************************************************************)
(** Properties of the injection from nat into Z *)

Theorem inj_S : (y:nat) (inject_nat (S y)) = (Zs (inject_nat y)).
Proof.
Induction y; [
  Unfold Zs ; Simpl; Trivial with arith
| Intros n; Intros H;
  Change (POS (add_un (anti_convert n)))=(Zs (inject_nat (S n)));
  Rewrite add_un_Zs; Trivial with arith].
Qed.
 
Theorem inj_plus : 
  (x,y:nat) (inject_nat (plus x y)) = (Zplus (inject_nat x) (inject_nat y)).
Proof.
Induction x; Induction y; [
  Simpl; Trivial with arith
| Simpl; Trivial with arith
| Simpl; Rewrite <- plus_n_O; Trivial with arith
| Intros m H1; Change (inject_nat (S (plus n (S m))))=
                        (Zplus (inject_nat (S n)) (inject_nat (S m)));
  Rewrite inj_S; Rewrite H; Do 2 Rewrite inj_S; Rewrite Zplus_S_n; Trivial with arith].
Qed.
 
Theorem inj_mult : 
  (x,y:nat) (inject_nat (mult x y)) = (Zmult (inject_nat x) (inject_nat y)).
Proof.
Induction x; [
  Simpl; Trivial with arith
| Intros n H y; Rewrite -> inj_S; Rewrite <- Zmult_Sm_n;
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

(**********************************************************************)
(** Moving terms from one side to the other of an inequality *)

Theorem Zne_left : (x,y:Z) (Zne x y) -> (Zne (Zplus x (Zopp y)) ZERO).
Proof.
Intros x y; Unfold Zne; Unfold not; Intros H1 H2; Apply H1;
Apply Zsimpl_plus_l with (Zopp y); Rewrite Zplus_inverse_l; Rewrite Zplus_sym;
Trivial with arith.
Qed.

Theorem Zegal_left : (x,y:Z) (x=y) -> (Zplus x (Zopp y)) = ZERO.
Proof.
Intros x y H;
Apply (Zsimpl_plus_l y);Rewrite -> Zplus_permute;
Rewrite -> Zplus_inverse_r;Do 2 Rewrite -> Zero_right;Assumption.
Qed.

Theorem Zle_left : (x,y:Z) (Zle x y) -> (Zle ZERO (Zplus y (Zopp x))).
Proof.
Intros x y H; Replace ZERO with (Zplus x (Zopp x)).
Apply Zle_reg_r; Trivial.
Apply Zplus_inverse_r.
Qed.

Theorem Zle_left_rev : (x,y:Z) (Zle ZERO (Zplus y (Zopp x))) 
	-> (Zle x y).
Proof.
Intros x y H; Apply (Zsimpl_le_plus_r (Zopp x)).
Rewrite Zplus_inverse_r; Trivial.
Qed.

Theorem Zlt_left_rev : (x,y:Z) (Zlt ZERO (Zplus y (Zopp x))) 
	-> (Zlt x y).
Proof.
Intros x y H; Apply Zsimpl_lt_plus_r with (Zopp x).
Rewrite Zplus_inverse_r; Trivial.
Qed.

Theorem Zlt_left :
  (x,y:Z) (Zlt x y) -> (Zle ZERO (Zplus (Zplus y (NEG xH)) (Zopp x))).
Proof.
Intros x y H; Apply Zle_left; Apply Zle_S_n; 
Change (Zle (Zs x) (Zs (Zpred y))); Rewrite <- Zs_pred; Apply Zlt_le_S;
Assumption.
Qed.

Theorem Zlt_left_lt :
  (x,y:Z) (Zlt x y) -> (Zlt ZERO (Zplus y (Zopp x))).
Proof.
Intros x y H; Replace ZERO with (Zplus x (Zopp x)).
Apply Zlt_reg_r; Trivial.
Apply Zplus_inverse_r.
Qed.

Theorem Zge_left : (x,y:Z) (Zge x y) -> (Zle ZERO (Zplus x (Zopp y))).
Proof.
Intros x y H; Apply Zle_left; Apply Zge_le; Assumption.
Qed.

Theorem Zgt_left :
  (x,y:Z) (Zgt x y) -> (Zle ZERO (Zplus (Zplus x (NEG xH)) (Zopp y))).
Proof.
Intros x y H; Apply Zlt_left; Apply Zgt_lt; Assumption.
Qed.

Theorem Zgt_left_gt :
  (x,y:Z) (Zgt x y) -> (Zgt (Zplus x (Zopp y)) ZERO).
Proof.
Intros x y H; Replace ZERO with (Zplus y (Zopp y)).
Apply Zgt_reg_r; Trivial.
Apply Zplus_inverse_r.
Qed.

Theorem Zgt_left_rev : (x,y:Z) (Zgt (Zplus x (Zopp y)) ZERO) 
	-> (Zgt x y).
Proof.
Intros x y H; Apply Zsimpl_gt_plus_r with (Zopp y).
Rewrite Zplus_inverse_r; Trivial.
Qed.

(**********************************************************************)
(** Misc lemmas *)

Theorem Zred_factor0 : (x:Z) x = (Zmult x (POS xH)).
Intro x; Rewrite (Zmult_n_1 x); Reflexivity.
Qed.

Theorem Zred_factor1 : (x:Z) (Zplus x x) = (Zmult x (POS (xO xH))).
Proof.
Exact Zplus_Zmult_2.
Qed.

Theorem Zred_factor2 :
  (x,y:Z) (Zplus x (Zmult x y)) = (Zmult x (Zplus (POS xH) y)).

Intros x y; Pattern 1 x ; Rewrite <- (Zmult_n_1 x);
Rewrite <- Zmult_plus_distr_r; Trivial with arith.
Qed.

Theorem Zred_factor3 :
  (x,y:Z) (Zplus (Zmult x y) x) = (Zmult x (Zplus (POS xH) y)).

Intros x y; Pattern 2 x ; Rewrite <- (Zmult_n_1 x);
Rewrite <- Zmult_plus_distr_r; Rewrite Zplus_sym; Trivial with arith.
Qed.
Theorem Zred_factor4 :
  (x,y,z:Z) (Zplus (Zmult x y) (Zmult x z)) = (Zmult x (Zplus y z)).
Intros x y z; Symmetry; Apply Zmult_plus_distr_r.
Qed.

Theorem Zred_factor5 : (x,y:Z) (Zplus (Zmult x ZERO) y) = y.

Intros x y; Rewrite <- Zmult_n_O;Auto with arith.
Qed.

Theorem Zred_factor6 : (x:Z) x = (Zplus x ZERO).

Intro; Rewrite Zero_right; Trivial with arith.
Qed.

Theorem Zle_mult_approx:
  (x,y,z:Z) (Zgt x ZERO) -> (Zgt z ZERO) -> (Zle ZERO y) -> 
    (Zle ZERO (Zplus (Zmult y x) z)).

Intros x y z H1 H2 H3; Apply Zle_trans with m:=(Zmult y x) ; [
  Apply Zle_mult; Assumption
| Pattern 1 (Zmult y x) ; Rewrite <- Zero_right; Apply Zle_reg_l;
  Apply Zlt_le_weak; Apply Zgt_lt; Assumption].
Qed.

Lemma Zgt_square_simpl: 
(x, y : Z) (Zge x ZERO) -> (Zge y ZERO) 
	-> (Zgt (Zmult x x) (Zmult y y)) -> (Zgt x y).
Intros x y H0 H1 H2.
Case (dec_Zlt y x).
Intro; Apply Zlt_gt; Trivial.
Intros H3; Cut (Zge y x).
Intros H.
Elim Zgt_not_le with 1 := H2.
Apply Zge_le.
Apply Zge_Zmult_pos_compat; Auto.
Apply not_Zlt; Trivial.
Qed.


Theorem Zmult_le_approx:
  (x,y,z:Z) (Zgt x ZERO) -> (Zgt x z) -> 
    (Zle ZERO (Zplus (Zmult y x) z)) -> (Zle ZERO y).

Intros x y z H1 H2 H3; Apply Zlt_n_Sm_le; Apply (Zmult_lt x); [
  Assumption
  | Apply Zle_lt_trans with 1:=H3 ; Rewrite <- Zmult_Sm_n;
    Apply Zlt_reg_l; Apply Zgt_lt; Assumption].

Qed.

V7only [Notation OMEGA2 := Zle_0_plus.].

