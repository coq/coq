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

V7only [
(* Compatibility *)
Require Znat.
Require Zcompare.
Notation neq := neq.
Notation Zne := Zne.
Notation OMEGA2 := Zle_0_plus.
Notation add_un_Zs := add_un_Zs.
Notation inj_S := inj_S.
Notation Zplus_S_n := Zplus_S_n.
Notation inj_plus := inj_plus.
Notation inj_mult := inj_mult.
Notation inj_neq := inj_neq.
Notation inj_le := inj_le.
Notation inj_lt := inj_lt.
Notation inj_gt := inj_gt.
Notation inj_ge := inj_ge.
Notation inj_eq := inj_eq.
Notation intro_Z := intro_Z.
Notation inj_minus1 := inj_minus1.
Notation inj_minus2 := inj_minus2.
Notation dec_eq := dec_eq.
Notation dec_Zne := dec_Zne.
Notation dec_Zle := dec_Zle.
Notation dec_Zgt := dec_Zgt.
Notation dec_Zge := dec_Zge.
Notation dec_Zlt := dec_Zlt.
Notation dec_eq_nat := dec_eq_nat.
Notation not_Zge := not_Zge.
Notation not_Zlt := not_Zlt.
Notation not_Zle := not_Zle.
Notation not_Zgt := not_Zgt.
Notation not_Zeq := not_Zeq.
Notation Zopp_one := Zopp_one.
Notation Zopp_Zmult_r := Zopp_Zmult_r.
Notation Zmult_Zopp_left := Zmult_Zopp_left.
Notation Zopp_Zmult_l := Zopp_Zmult_l.
Notation Zcompare_Zplus_compatible2 := Zcompare_Zplus_compatible2.
Notation Zcompare_Zmult_compatible := Zcompare_Zmult_compatible.
Notation Zmult_eq := Zmult_eq.
Notation Z_eq_mult := Z_eq_mult.
Notation Zmult_le := Zmult_le.
Notation Zle_ZERO_mult := Zle_ZERO_mult.
Notation Zgt_ZERO_mult := Zgt_ZERO_mult.
Notation Zle_mult := Zle_mult.
Notation Zmult_lt := Zmult_lt.
Notation Zmult_gt := Zmult_gt.
Notation Zle_Zmult_pos_right := Zle_Zmult_pos_right.
Notation Zle_Zmult_pos_left := Zle_Zmult_pos_left.
Notation Zge_Zmult_pos_right := Zge_Zmult_pos_right.
Notation Zge_Zmult_pos_left := Zge_Zmult_pos_left.
Notation Zge_Zmult_pos_compat := Zge_Zmult_pos_compat.
Notation Zle_mult_simpl := Zle_mult_simpl.
Notation Zge_mult_simpl := Zge_mult_simpl.
Notation Zgt_mult_simpl := Zgt_mult_simpl.
Notation Zgt_square_simpl := Zgt_square_simpl.
].
