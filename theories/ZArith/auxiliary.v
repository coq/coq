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
Require BinInt.
Require Zorder.
Require Decidable.
Require Peano_dec.
Require Export Compare_dec.

Open Local Scope Z_scope.

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
Intros x y H; Apply Zsimpl_le_plus_r with (Zopp x).
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
(** Factorization lemmas *)

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

Theorem Zmult_le_approx:
  (x,y,z:Z) (Zgt x ZERO) -> (Zgt x z) -> 
    (Zle ZERO (Zplus (Zmult y x) z)) -> (Zle ZERO y).

Intros x y z H1 H2 H3; Apply Zlt_n_Sm_le; Apply Zmult_lt with x; [
  Assumption
  | Apply Zle_lt_trans with 1:=H3 ; Rewrite <- Zmult_Sm_n;
    Apply Zlt_reg_l; Apply Zgt_lt; Assumption].

Qed.

V7only [Notation OMEGA2 := Zle_0_plus.].

