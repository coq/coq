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
Require zarith_aux.
Require Decidable.
Require Peano_dec.
Require Export Compare_dec.


Definition neq := [x,y:nat] ~(x=y).
Definition Zne := [x,y:Z] ~(x=y).
Theorem add_un_Zs : (x:positive) (POS (add_un x)) = (Zs (POS x)).
Intro; Rewrite -> ZL12; Unfold Zs; Simpl; Trivial with arith.
Qed.

Theorem inj_S : (y:nat) (inject_nat (S y)) = (Zs (inject_nat y)).
Induction y; [
  Unfold Zs ; Simpl; Trivial with arith
| Intros n; Intros H;
  Change (POS (add_un (anti_convert n)))=(Zs (inject_nat (S n)));
  Rewrite add_un_Zs; Trivial with arith].
Qed.
 
Theorem Zplus_S_n: (x,y:Z) (Zplus (Zs x) y) = (Zs (Zplus x y)).
Intros x y; Unfold Zs; Rewrite (Zplus_sym (Zplus x y)); Rewrite Zplus_assoc;
Rewrite (Zplus_sym (POS xH)); Trivial with arith.
Qed.

Theorem inj_plus : 
  (x,y:nat) (inject_nat (plus x y)) = (Zplus (inject_nat x) (inject_nat y)).

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

Induction x; [
  Simpl; Trivial with arith
| Intros n H y; Rewrite -> inj_S; Rewrite <- Zmult_Sm_n;
    Rewrite <- H;Rewrite <- inj_plus; Simpl; Rewrite plus_sym; Trivial with arith].
Qed.

Theorem inj_neq:
  (x,y:nat) (neq x y) -> (Zne (inject_nat x) (inject_nat y)).

Unfold neq Zne not ; Intros x y H1 H2; Apply H1; Generalize H2; 
Case x; Case y; Intros; [
  Auto with arith
| Discriminate H0
| Discriminate H0
| Simpl in H0; Injection H0; Do 2 Rewrite <- bij1; Intros E; Rewrite E; Auto with arith].
Qed. 

Theorem inj_le:
  (x,y:nat) (le x y) -> (Zle (inject_nat x) (inject_nat y)).

Intros x y; Intros H; Elim H; [
  Unfold Zle ; Elim (Zcompare_EGAL (inject_nat x) (inject_nat x));
  Intros H1 H2; Rewrite H2; [ Discriminate | Trivial with arith]
| Intros m H1 H2; Apply Zle_trans with (inject_nat m); 
    [Assumption | Rewrite inj_S; Apply Zle_n_Sn]].
Qed.

Theorem inj_lt: (x,y:nat) (lt x y) -> (Zlt (inject_nat x) (inject_nat y)).
Intros x y H; Apply Zgt_lt; Apply Zle_S_gt; Rewrite <- inj_S; Apply inj_le;
Exact H.
Qed.

Theorem inj_gt: (x,y:nat) (gt x y) -> (Zgt (inject_nat x) (inject_nat y)).
Intros x y H; Apply Zlt_gt; Apply inj_lt; Exact H.
Qed.

Theorem inj_ge: (x,y:nat) (ge x y) -> (Zge (inject_nat x) (inject_nat y)).
Intros x y H; Apply Zle_ge; Apply inj_le; Apply H.
Qed.

Theorem inj_eq: (x,y:nat) x=y -> (inject_nat x) = (inject_nat y).
Intros x y H; Rewrite H; Trivial with arith.
Qed.

Theorem intro_Z : 
  (x:nat) (EX y:Z | (inject_nat x)=y /\ 
      	  (Zle ZERO (Zplus (Zmult y (POS xH)) ZERO))).
Intros x; Exists (inject_nat x); Split; [
  Trivial with arith
| Rewrite Zmult_sym; Rewrite Zmult_one; Rewrite Zero_right; 
  Unfold Zle ; Elim x; Intros;Simpl; Discriminate ].
Qed.

Theorem inj_minus1 :
  (x,y:nat) (le y x) -> 
    (inject_nat (minus x y)) = (Zminus (inject_nat x) (inject_nat y)).
Intros x y H; Apply (Zsimpl_plus_l (inject_nat y)); Unfold Zminus ;
Rewrite Zplus_permute; Rewrite Zplus_inverse_r; Rewrite <- inj_plus;
Rewrite <- (le_plus_minus y x H);Rewrite Zero_right; Trivial with arith.
Qed.
 
Theorem inj_minus2: (x,y:nat) (gt y x) -> (inject_nat (minus x y)) = ZERO.
Intros x y H; Rewrite inj_minus_aux; [ Trivial with arith | Apply gt_not_le; Assumption].
Qed.

Theorem dec_eq: (x,y:Z) (decidable (x=y)).
Intros x y; Unfold decidable ; Elim (Zcompare_EGAL x y);
Intros H1 H2; Elim (Dcompare (Zcompare x y)); [
    Tauto
  | Intros H3; Right; Unfold not ; Intros H4;
    Elim H3; Rewrite (H2 H4); Intros H5; Discriminate H5].
Qed. 

Theorem dec_Zne: (x,y:Z) (decidable (Zne x y)).
Intros x y; Unfold decidable Zne ; Elim (Zcompare_EGAL x y).
Intros H1 H2; Elim (Dcompare (Zcompare x y)); 
  [ Right; Rewrite H1; Auto
  | Left; Unfold not; Intro; Absurd (Zcompare x y)=EGAL; 
    [ Elim H; Intros HR; Rewrite HR; Discriminate 
    | Auto]].
Qed.

Theorem dec_Zle: (x,y:Z) (decidable (Zle x y)).
Intros x y; Unfold decidable Zle ; Elim (Zcompare x y); [
    Left; Discriminate
  | Left; Discriminate
  | Right; Unfold not ; Intros H; Apply H; Trivial with arith].
Qed.

Theorem dec_Zgt: (x,y:Z) (decidable (Zgt x y)).
Intros x y; Unfold decidable Zgt ; Elim (Zcompare x y);
  [ Right; Discriminate | Right; Discriminate | Auto with arith].
Qed.

Theorem dec_Zge: (x,y:Z) (decidable (Zge x y)).
Intros x y; Unfold decidable Zge ; Elim (Zcompare x y); [
  Left; Discriminate
| Right; Unfold not ; Intros H; Apply H; Trivial with arith
| Left; Discriminate]. 
Qed.

Theorem dec_Zlt: (x,y:Z) (decidable (Zlt x y)).
Intros x y; Unfold decidable Zlt ; Elim (Zcompare x y);
  [ Right; Discriminate | Auto with arith | Right; Discriminate].
Qed.

Theorem not_Zge : (x,y:Z) ~(Zge x y) -> (Zlt x y).
Unfold Zge Zlt ; Intros x y H; Apply dec_not_not;
  [ Exact (dec_Zlt x y) | Assumption].
Qed.
 
Theorem not_Zlt : (x,y:Z) ~(Zlt x y) -> (Zge x y).
Unfold Zlt Zge; Auto with arith.
Qed.

Theorem not_Zle : (x,y:Z) ~(Zle x y) -> (Zgt x y).
Unfold Zle Zgt ; Intros x y H; Apply dec_not_not;
  [ Exact (dec_Zgt x y) | Assumption].
 Qed.
 
Theorem not_Zgt : (x,y:Z) ~(Zgt x y) -> (Zle x y).
Unfold Zgt Zle; Auto with arith.
Qed.

Theorem not_Zeq : (x,y:Z) ~ x=y -> (Zlt x y) \/ (Zlt y x).

Intros x y; Elim (Dcompare (Zcompare x y)); [
  Intros H1 H2; Absurd x=y; [ Assumption | Elim (Zcompare_EGAL x y); Auto with arith]
| Unfold Zlt ; Intros H; Elim H; Intros H1; 
    [Auto with arith | Right; Elim (Zcompare_ANTISYM x y); Auto with arith]].
Qed. 

Lemma new_var: (x:Z) (EX y:Z |(x=y)).
Intros x; Exists x; Trivial with arith. 
Qed.

Theorem Zne_left : (x,y:Z) (Zne x y) -> (Zne (Zplus x (Zopp y)) ZERO).
Intros x y; Unfold Zne; Unfold not; Intros H1 H2; Apply H1;
Apply Zsimpl_plus_l with (Zopp y); Rewrite Zplus_inverse_l; Rewrite Zplus_sym;
Trivial with arith.
Qed.

Theorem Zegal_left : (x,y:Z) (x=y) -> (Zplus x (Zopp y)) = ZERO.
Intros x y H;
Apply (Zsimpl_plus_l y);Rewrite -> Zplus_permute;
Rewrite -> Zplus_inverse_r;Do 2 Rewrite -> Zero_right;Assumption.
Qed.

Theorem Zle_left : (x,y:Z) (Zle x y) -> (Zle ZERO (Zplus y (Zopp x))).
Intros x y H; Replace ZERO with (Zplus x (Zopp x)).
Apply Zle_reg_r; Trivial.
Apply Zplus_inverse_r.
Qed.

Theorem Zle_left_rev : (x,y:Z) (Zle ZERO (Zplus y (Zopp x))) 
	-> (Zle x y).
Intros x y H; Apply (Zsimpl_le_plus_r (Zopp x)).
Rewrite Zplus_inverse_r; Trivial.
Qed.

Theorem Zlt_left_rev : (x,y:Z) (Zlt ZERO (Zplus y (Zopp x))) 
	-> (Zlt x y).
Intros x y H; Apply Zsimpl_lt_plus_r with (Zopp x).
Rewrite Zplus_inverse_r; Trivial.
Qed.

Theorem Zlt_left :
  (x,y:Z) (Zlt x y) -> (Zle ZERO (Zplus (Zplus y (NEG xH)) (Zopp x))).
Intros x y H; Apply Zle_left; Apply Zle_S_n; 
Change (Zle (Zs x) (Zs (Zpred y))); Rewrite <- Zs_pred; Apply Zlt_le_S;
Assumption.
Qed.

Theorem Zlt_left_lt :
  (x,y:Z) (Zlt x y) -> (Zlt ZERO (Zplus y (Zopp x))).
Intros x y H; Replace ZERO with (Zplus x (Zopp x)).
Apply Zlt_reg_r; Trivial.
Apply Zplus_inverse_r.
Qed.

Theorem Zge_left : (x,y:Z) (Zge x y) -> (Zle ZERO (Zplus x (Zopp y))).
Intros x y H; Apply Zle_left; Apply Zge_le; Assumption.
Qed.

Theorem Zgt_left :
  (x,y:Z) (Zgt x y) -> (Zle ZERO (Zplus (Zplus x (NEG xH)) (Zopp y))).
Intros x y H; Apply Zlt_left; Apply Zgt_lt; Assumption.
Qed.

Theorem Zgt_left_gt :
  (x,y:Z) (Zgt x y) -> (Zgt (Zplus x (Zopp y)) ZERO).
Intros x y H; Replace ZERO with (Zplus y (Zopp y)).
Apply Zgt_reg_r; Trivial.
Apply Zplus_inverse_r.
Qed.

Theorem Zgt_left_rev : (x,y:Z) (Zgt (Zplus x (Zopp y)) ZERO) 
	-> (Zgt x y).
Intros x y H; Apply Zsimpl_gt_plus_r with (Zopp y).
Rewrite Zplus_inverse_r; Trivial.
Qed.

Theorem Zopp_one : (x:Z)(Zopp x)=(Zmult x (NEG xH)).
Induction x; Intros; Rewrite Zmult_sym; Auto with arith.
Qed.

Theorem Zopp_Zmult_r : (x,y:Z)(Zopp (Zmult x y)) = (Zmult x (Zopp y)).
Intros x y; Rewrite Zmult_sym; Rewrite <- Zopp_Zmult; Apply Zmult_sym.
Qed.

Theorem Zmult_Zopp_left :  (x,y:Z)(Zmult (Zopp x) y) = (Zmult x (Zopp y)).
Intros; Rewrite Zopp_Zmult; Rewrite Zopp_Zmult_r; Trivial with arith.
Qed.

Theorem Zopp_Zmult_l : (x,y:Z)(Zopp (Zmult x y)) = (Zmult (Zopp x) y).
Intros x y; Symmetry; Apply Zopp_Zmult.
Qed.

Theorem Zred_factor0 : (x:Z) x = (Zmult x (POS xH)).
Intro x; Rewrite (Zmult_n_1 x); Trivial with arith.
Qed.

Theorem Zred_factor1 : (x:Z) (Zplus x x) = (Zmult x (POS (xO xH))).
Intros x; Pattern 1 2 x ; Rewrite <- (Zmult_n_1 x);
Rewrite <- Zmult_plus_distr_r; Auto with arith.
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

Theorem Zcompare_Zplus_compatible2 :
  (r:relation)(x,y,z,t:Z)
    (Zcompare x y) = r -> (Zcompare z t) = r ->
    (Zcompare (Zplus x z) (Zplus y t)) = r.

Intros r x y z t; Case r; [
  Intros H1 H2; Elim (Zcompare_EGAL x y); Elim (Zcompare_EGAL z t);
  Intros H3 H4 H5 H6; Rewrite H3; [ 
    Rewrite H5; [ Elim (Zcompare_EGAL (Zplus y t) (Zplus y t)); Auto with arith | Auto with arith ]
  | Auto with arith ]
| Intros H1 H2; Elim (Zcompare_ANTISYM (Zplus y t) (Zplus x z));
  Intros H3 H4; Apply H3;
  Apply Zcompare_trans_SUPERIEUR with y:=(Zplus y z) ; [
    Rewrite Zcompare_Zplus_compatible;
    Elim (Zcompare_ANTISYM t z); Auto with arith
  | Do 2 Rewrite <- (Zplus_sym z); 
    Rewrite Zcompare_Zplus_compatible;
    Elim (Zcompare_ANTISYM y x); Auto with arith]
| Intros H1 H2;
  Apply Zcompare_trans_SUPERIEUR with y:=(Zplus x t) ; [
    Rewrite Zcompare_Zplus_compatible; Assumption
  | Do 2 Rewrite <- (Zplus_sym t);
    Rewrite Zcompare_Zplus_compatible; Assumption]].
Qed.

Theorem Zcompare_Zmult_compatible : 
   (x:positive)(y,z:Z)
      (Zcompare (Zmult (POS x) y) (Zmult (POS x) z)) = (Zcompare y z).

Induction x; [
  Intros p H y z;
  Cut (POS (xI p))=(Zplus (Zplus (POS p) (POS p)) (POS xH)); [
    Intros E; Rewrite E; Do 4 Rewrite Zmult_plus_distr_l; 
    Do 2 Rewrite Zmult_one;
    Apply Zcompare_Zplus_compatible2; [
      Apply Zcompare_Zplus_compatible2; Apply H
    | Trivial with arith]
  | Simpl; Rewrite (add_x_x p); Trivial with arith]
| Intros p H y z; Cut (POS (xO p))=(Zplus (POS p) (POS p)); [
    Intros E; Rewrite E; Do 2 Rewrite Zmult_plus_distr_l;
      Apply Zcompare_Zplus_compatible2; Apply H
    | Simpl; Rewrite (add_x_x p); Trivial with arith]
  | Intros y z; Do 2 Rewrite Zmult_one; Trivial with arith].
Qed.

Theorem Zmult_eq:
  (x,y:Z) ~(x=ZERO) -> (Zmult y x) = ZERO -> y = ZERO.

Intros x y; Case x; [
  Intro; Absurd ZERO=ZERO; Auto with arith
| Intros p H1 H2; Elim (Zcompare_EGAL y ZERO);
  Intros H3 H4; Apply H3; Rewrite <- (Zcompare_Zmult_compatible p);
  Rewrite -> Zero_mult_right; Rewrite -> Zmult_sym;
  Elim (Zcompare_EGAL (Zmult y (POS p)) ZERO); Auto with arith
| Intros p H1 H2; Apply Zopp_intro; Simpl;
  Elim (Zcompare_EGAL (Zopp y) ZERO); Intros H3 H4; Apply H3;
  Rewrite <- (Zcompare_Zmult_compatible p);
  Rewrite -> Zero_mult_right; Rewrite -> Zmult_sym;
  Rewrite -> Zmult_Zopp_left; Simpl;
  Elim (Zcompare_EGAL (Zmult y (NEG p)) ZERO); Auto with arith].
Qed.

Theorem Z_eq_mult:
  (x,y:Z)  y = ZERO -> (Zmult y x) = ZERO.
Intros x y H; Rewrite H; Auto with arith.
Qed.

Theorem Zmult_le:
  (x,y:Z) (Zgt x ZERO) -> (Zle ZERO (Zmult y x)) -> (Zle ZERO y).

Intros x y; Case x; [
  Simpl; Unfold Zgt ; Simpl; Intros H; Discriminate H
| Intros p H1; Unfold Zle; Rewrite -> Zmult_sym;
  Pattern 1 ZERO ; Rewrite <- (Zero_mult_right (POS p));
  Rewrite  Zcompare_Zmult_compatible; Auto with arith
| Intros p; Unfold Zgt ; Simpl; Intros H; Discriminate H].
Qed.

Theorem Zle_ZERO_mult : 
	 (x,y:Z) (Zle ZERO x) -> (Zle ZERO y) -> (Zle ZERO (Zmult x y)).
Intros x y; Case x.
Intros; Rewrite Zero_mult_left; Trivial.
Intros p H1; Unfold Zle.
  Pattern 2 ZERO ; Rewrite <- (Zero_mult_right (POS p)).
  Rewrite  Zcompare_Zmult_compatible; Trivial.
Intros p H1 H2; Absurd (Zgt ZERO (NEG p)); Trivial.
Unfold Zgt; Simpl; Auto with zarith.
Qed.

Lemma Zgt_ZERO_mult: (a,b:Z) (Zgt a ZERO)->(Zgt b ZERO)
	->(Zgt (Zmult a b) ZERO).
Intros x y; Case x.
Intros H; Discriminate H.
Intros p H1; Unfold Zgt; 
Pattern 2 ZERO ; Rewrite <- (Zero_mult_right (POS p)).
  Rewrite  Zcompare_Zmult_compatible; Trivial.
Intros p H; Discriminate H.
Qed.

Theorem Zle_mult:
  (x,y:Z) (Zgt x ZERO) -> (Zle ZERO y) -> (Zle ZERO (Zmult y x)).
Intros x y H1 H2; Apply Zle_ZERO_mult; Trivial.
Apply Zlt_le_weak; Apply Zgt_lt; Trivial.
Qed.

Theorem Zmult_lt:
  (x,y:Z) (Zgt x ZERO) -> (Zlt ZERO (Zmult y x)) -> (Zlt ZERO y).

Intros x y; Case x; [
  Simpl; Unfold Zgt ; Simpl; Intros H; Discriminate H
| Intros p H1; Unfold Zlt; Rewrite -> Zmult_sym;
  Pattern 1 ZERO ; Rewrite <- (Zero_mult_right (POS p));
  Rewrite  Zcompare_Zmult_compatible; Auto with arith
| Intros p; Unfold Zgt ; Simpl; Intros H; Discriminate H].
Qed.

Theorem Zmult_gt:
  (x,y:Z) (Zgt x ZERO) -> (Zgt (Zmult x y) ZERO) -> (Zgt y ZERO).

Intros x y; Case x.
 Intros H; Discriminate H.
 Intros p H1; Unfold Zgt.
 Pattern 1 ZERO ; Rewrite <- (Zero_mult_right (POS p)).
 Rewrite  Zcompare_Zmult_compatible; Trivial.
Intros p H; Discriminate H.
Qed.

Theorem Zle_mult_approx:
  (x,y,z:Z) (Zgt x ZERO) -> (Zgt z ZERO) -> (Zle ZERO y) -> 
    (Zle ZERO (Zplus (Zmult y x) z)).

Intros x y z H1 H2 H3; Apply Zle_trans with m:=(Zmult y x) ; [
  Apply Zle_mult; Assumption
| Pattern 1 (Zmult y x) ; Rewrite <- Zero_right; Apply Zle_reg_l;
  Apply Zlt_le_weak; Apply Zgt_lt; Assumption].
Qed.

Lemma Zle_Zmult_pos_right : 
	(a,b,c : Z) 
	(Zle a b) -> (Zle ZERO c) -> (Zle (Zmult a c) (Zmult b c)).
Intros a b c H1 H2; Apply Zle_left_rev.
Rewrite Zopp_Zmult_l.
Rewrite <- Zmult_plus_distr_l.
Apply Zle_ZERO_mult; Trivial.
Apply Zle_left; Trivial.
Qed.

Lemma Zle_Zmult_pos_left : 
	(a,b,c : Z) 
	(Zle a b) -> (Zle ZERO c) -> (Zle (Zmult c a) (Zmult c b)).
Intros a b c H1 H2; Rewrite (Zmult_sym c a);Rewrite (Zmult_sym c b).
Apply  Zle_Zmult_pos_right; Trivial.
Qed.

Lemma Zge_Zmult_pos_right : 
	(a,b,c : Z) 
	(Zge a b) -> (Zge c ZERO) -> (Zge (Zmult a c) (Zmult b c)).
Intros a b c H1 H2; Apply Zle_ge.
Apply Zle_Zmult_pos_right; Apply Zge_le; Trivial.
Qed.

Lemma Zge_Zmult_pos_left : 
	(a,b,c : Z) 
	(Zge a b) -> (Zge c ZERO) -> (Zge (Zmult c a) (Zmult c b)).
Intros a b c H1 H2; Apply Zle_ge.
Apply Zle_Zmult_pos_left; Apply Zge_le; Trivial.
Qed.

Lemma Zge_Zmult_pos_compat : 
	(a,b,c,d : Z) 
	(Zge a c) -> (Zge b d) -> (Zge c ZERO) -> (Zge d ZERO) 
	-> (Zge (Zmult a b) (Zmult c d)).
Intros a b c d H0 H1 H2 H3.
Apply Zge_trans with (Zmult a d).
Apply Zge_Zmult_pos_left; Trivial.
Apply Zge_trans with c; Trivial. 
Apply Zge_Zmult_pos_right; Trivial.
Qed.

Lemma Zle_mult_simpl 
 : (a,b,c:Z) (Zgt c ZERO)->(Zle (Zmult a c) (Zmult b c))->(Zle a b).
Intros a b c H1 H2; Apply Zle_left_rev.
Apply Zmult_le with c; Trivial.
Rewrite Zmult_plus_distr_l.
Rewrite <- Zopp_Zmult_l.
Apply Zle_left; Trivial.
Qed.


Lemma Zge_mult_simpl 
 : (a,b,c:Z) (Zgt c ZERO)->(Zge (Zmult a c) (Zmult b c))->(Zge a b).
Intros a b c H1 H2; Apply Zle_ge; Apply Zle_mult_simpl with c; Trivial.
Apply Zge_le; Trivial.
Qed.

Lemma Zgt_mult_simpl 
 : (a,b,c:Z) (Zgt c ZERO)->(Zgt (Zmult a c) (Zmult b c))->(Zgt a b).
Intros a b c H1 H2; Apply Zgt_left_rev.
Apply Zmult_gt with c; Trivial.
Rewrite Zmult_sym.
Rewrite Zmult_plus_distr_l.
Rewrite <- Zopp_Zmult_l.
Apply Zgt_left_gt; Trivial.
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

Theorem OMEGA1 : (x,y:Z) (x=y) -> (Zle ZERO x) -> (Zle ZERO y).
Intros x y H; Rewrite H; Auto with arith.
Qed.

Theorem OMEGA2 : (x,y:Z) (Zle ZERO x) -> (Zle ZERO y) -> (Zle ZERO (Zplus x y)).
Intros x y H1 H2;Rewrite <- (Zero_left ZERO); Apply Zle_plus_plus; Assumption.
Qed. 

Theorem OMEGA3 : 
  (x,y,k:Z)(Zgt k ZERO)-> (x=(Zmult y k)) -> (x=ZERO) -> (y=ZERO).

Intros x y k H1 H2 H3; Apply (Zmult_eq k); [
  Unfold not ; Intros H4; Absurd (Zgt k ZERO); [
    Rewrite H4; Unfold Zgt ; Simpl; Discriminate | Assumption]
  | Rewrite <- H2; Assumption].
Qed.

Theorem OMEGA4 :
  (x,y,z:Z)(Zgt x ZERO) -> (Zgt y x) -> ~(Zplus (Zmult z y) x) = ZERO.

Unfold not ; Intros x y z H1 H2 H3; Cut (Zgt y ZERO); [
  Intros H4; Cut (Zle ZERO (Zplus (Zmult z y) x)); [
    Intros H5; Generalize (Zmult_le_approx y z x H4 H2 H5) ; Intros H6;
    Absurd (Zgt (Zplus (Zmult z y) x) ZERO); [
      Rewrite -> H3; Unfold Zgt ; Simpl; Discriminate
    | Apply Zle_gt_trans with x ; [
        Pattern 1 x ; Rewrite <- (Zero_left x); Apply Zle_reg_r;
        Rewrite -> Zmult_sym; Generalize H4 ; Unfold Zgt;
        Case y; [
          Simpl; Intros H7; Discriminate H7
        | Intros p H7; Rewrite <- (Zero_mult_right (POS p));
          Unfold Zle ; Rewrite -> Zcompare_Zmult_compatible; Exact H6
        | Simpl; Intros p H7; Discriminate H7]
      | Assumption]]
    | Rewrite -> H3; Unfold Zle ; Simpl; Discriminate]
  | Apply Zgt_trans with x ; [ Assumption | Assumption]].
Qed.

Theorem OMEGA5: (x,y,z:Z)(x=ZERO) -> (y=ZERO) -> (Zplus x (Zmult y z)) = ZERO.

Intros x y z H1 H2; Rewrite H1; Rewrite H2; Simpl; Trivial with arith.
Qed.
Theorem OMEGA6:
  (x,y,z:Z)(Zle ZERO x) -> (y=ZERO) -> (Zle ZERO (Zplus x (Zmult y z))).

Intros x y z H1 H2; Rewrite H2; Simpl; Rewrite Zero_right; Assumption.
Qed.

Theorem OMEGA7:
  (x,y,z,t:Z)(Zgt z ZERO) -> (Zgt t ZERO) -> (Zle ZERO x) -> (Zle ZERO y) -> 
    (Zle ZERO (Zplus (Zmult x z) (Zmult y t))).

Intros x y z t H1 H2 H3 H4; Rewrite <- (Zero_left ZERO);
Apply Zle_plus_plus; Apply Zle_mult; Assumption.
Qed.

Theorem OMEGA8: 
  (x,y:Z) (Zle ZERO x) -> (Zle ZERO y) -> x = (Zopp y) -> x = ZERO.

Intros x y H1 H2 H3; Elim (Zle_lt_or_eq ZERO x H1); [
  Intros H4; Absurd (Zlt ZERO x); [
    Change (Zge ZERO x); Apply Zle_ge; Apply (Zsimpl_le_plus_l y);
    Rewrite -> H3; Rewrite Zplus_inverse_r; Rewrite Zero_right; Assumption
  | Assumption]
| Intros H4; Rewrite -> H4; Trivial with arith].
Qed.

Theorem OMEGA9:(x,y,z,t:Z) y=ZERO -> x = z -> 
  (Zplus y (Zmult (Zplus (Zopp x) z) t)) = ZERO.

Intros x y z t H1 H2; Rewrite H2; Rewrite Zplus_inverse_l; 
Rewrite Zero_mult_left;  Rewrite Zero_right; Assumption.
Qed.
Theorem OMEGA10:(v,c1,c2,l1,l2,k1,k2:Z)
  (Zplus (Zmult (Zplus (Zmult v c1) l1) k1) (Zmult (Zplus (Zmult v c2) l2) k2))
  = (Zplus (Zmult v (Zplus (Zmult c1 k1) (Zmult c2 k2)))
           (Zplus (Zmult l1 k1) (Zmult l2 k2))).

Intros; Repeat (Rewrite Zmult_plus_distr_l Orelse Rewrite Zmult_plus_distr_r);
Repeat Rewrite Zmult_assoc; Repeat Elim Zplus_assoc; 
Rewrite (Zplus_permute (Zmult l1 k1) (Zmult (Zmult v c2) k2)); Trivial with arith.
Qed.

Theorem OMEGA11:(v1,c1,l1,l2,k1:Z)
  (Zplus (Zmult (Zplus (Zmult v1 c1) l1) k1) l2)
  = (Zplus (Zmult v1 (Zmult c1 k1)) (Zplus (Zmult l1 k1) l2)).

Intros; Repeat (Rewrite Zmult_plus_distr_l Orelse Rewrite Zmult_plus_distr_r);
Repeat Rewrite Zmult_assoc; Repeat Elim Zplus_assoc; Trivial with arith.
Qed.

Theorem OMEGA12:(v2,c2,l1,l2,k2:Z)
  (Zplus l1 (Zmult (Zplus (Zmult v2 c2) l2) k2))
  = (Zplus (Zmult v2 (Zmult c2 k2)) (Zplus l1 (Zmult l2 k2))).

Intros; Repeat (Rewrite Zmult_plus_distr_l Orelse Rewrite Zmult_plus_distr_r);
Repeat Rewrite Zmult_assoc; Repeat Elim Zplus_assoc; Rewrite Zplus_permute;
Trivial with arith.
Qed.

Theorem OMEGA13:(v,l1,l2:Z)(x:positive)
  (Zplus (Zplus (Zmult v (POS x)) l1) (Zplus (Zmult v (NEG x)) l2))
  = (Zplus l1 l2).

Intros; Rewrite  Zplus_assoc; Rewrite (Zplus_sym (Zmult v (POS x)) l1);
Rewrite (Zplus_assoc_r l1); Rewrite <- Zmult_plus_distr_r;
Rewrite <- Zopp_NEG; Rewrite (Zplus_sym (Zopp (NEG x)) (NEG x));
Rewrite Zplus_inverse_r; Rewrite  Zero_mult_right; Rewrite Zero_right; Trivial with arith.
Qed.
 
Theorem OMEGA14:(v,l1,l2:Z)(x:positive)
  (Zplus (Zplus (Zmult v (NEG x)) l1) (Zplus (Zmult v (POS x)) l2))
  = (Zplus l1 l2).

Intros; Rewrite  Zplus_assoc; Rewrite (Zplus_sym (Zmult v (NEG x)) l1);
Rewrite (Zplus_assoc_r l1); Rewrite <- Zmult_plus_distr_r;
Rewrite <- Zopp_NEG; Rewrite  Zplus_inverse_r; Rewrite  Zero_mult_right;
Rewrite Zero_right; Trivial with arith.
Qed.
Theorem OMEGA15:(v,c1,c2,l1,l2,k2:Z)
  (Zplus (Zplus (Zmult v c1) l1) (Zmult (Zplus (Zmult v c2) l2) k2))
  = (Zplus (Zmult v (Zplus c1  (Zmult c2 k2)))
           (Zplus l1 (Zmult l2 k2))).

Intros; Repeat (Rewrite Zmult_plus_distr_l Orelse Rewrite Zmult_plus_distr_r);
Repeat Rewrite Zmult_assoc; Repeat Elim Zplus_assoc; 
Rewrite (Zplus_permute l1 (Zmult (Zmult v c2) k2)); Trivial with arith.
Qed.

Theorem OMEGA16:
  (v,c,l,k:Z)
   (Zmult (Zplus (Zmult v c) l) k) = (Zplus (Zmult v (Zmult c k)) (Zmult l k)).

Intros; Repeat (Rewrite Zmult_plus_distr_l Orelse Rewrite Zmult_plus_distr_r);
Repeat Rewrite Zmult_assoc; Repeat Elim Zplus_assoc; Trivial with arith.
Qed.

Theorem OMEGA17: 
  (x,y,z:Z)(Zne x ZERO) -> (y=ZERO) -> (Zne (Zplus x (Zmult y z)) ZERO).

Unfold Zne not; Intros x y z H1 H2 H3; Apply H1; 
Apply Zsimpl_plus_l with (Zmult y z); Rewrite Zplus_sym; Rewrite H3; 
Rewrite H2; Auto with arith.
Qed.

Theorem OMEGA18:
  (x,y,k:Z) (x=(Zmult y k)) -> (Zne x ZERO) -> (Zne y ZERO).

Unfold Zne not; Intros x y k H1 H2 H3; Apply H2; Rewrite H1; Rewrite H3; Auto with arith.
Qed.

Theorem OMEGA19:
  (x:Z) (Zne x ZERO) -> 
    (Zle ZERO (Zplus x (NEG xH))) \/ (Zle ZERO (Zplus (Zmult x (NEG xH)) (NEG xH))).

Unfold Zne ; Intros x H; Elim (Zle_or_lt ZERO x); [
  Intros H1; Elim Zle_lt_or_eq with 1:=H1; [
    Intros H2; Left;  Change (Zle ZERO (Zpred x)); Apply Zle_S_n;
    Rewrite <- Zs_pred; Apply Zlt_le_S; Assumption
  | Intros H2; Absurd x=ZERO; Auto with arith]
| Intros H1; Right; Rewrite <- Zopp_one; Rewrite Zplus_sym;
  Apply Zle_left; Apply Zle_S_n; Simpl; Apply Zlt_le_S; Auto with arith].
Qed.

Theorem OMEGA20:
  (x,y,z:Z)(Zne x  ZERO) -> (y=ZERO) -> (Zne (Zplus x (Zmult y z)) ZERO).

Unfold Zne not; Intros x y z H1 H2 H3; Apply H1; Rewrite H2 in H3;
Simpl in H3; Rewrite Zero_right in H3; Trivial with arith.
Qed.

Definition fast_Zplus_sym := 
[x,y:Z][P:Z -> Prop][H: (P (Zplus y x))]
  (eq_ind_r Z (Zplus y x) P H (Zplus x y) (Zplus_sym x y)).

Definition fast_Zplus_assoc_r :=
[n,m,p:Z][P:Z -> Prop][H : (P (Zplus n (Zplus m p)))]
 (eq_ind_r Z (Zplus n (Zplus m p)) P H (Zplus (Zplus n m) p) (Zplus_assoc_r n m p)).

Definition fast_Zplus_assoc_l :=
[n,m,p:Z][P:Z -> Prop][H : (P (Zplus (Zplus n m) p))]
 (eq_ind_r Z (Zplus (Zplus n m) p) P H (Zplus n (Zplus m p)) 
           (Zplus_assoc_l n m p)).

Definition fast_Zplus_permute :=
[n,m,p:Z][P:Z -> Prop][H : (P (Zplus m (Zplus n p)))]
 (eq_ind_r Z (Zplus m (Zplus n p)) P H (Zplus n (Zplus m p))
           (Zplus_permute n m p)).

Definition fast_OMEGA10 := 
[v,c1,c2,l1,l2,k1,k2:Z][P:Z -> Prop]
[H : (P (Zplus (Zmult v (Zplus (Zmult c1 k1) (Zmult c2 k2)))
               (Zplus (Zmult l1 k1) (Zmult l2 k2))))]
 (eq_ind_r Z 
           (Zplus (Zmult v (Zplus (Zmult c1 k1) (Zmult c2 k2)))
            (Zplus (Zmult l1 k1) (Zmult l2 k2)))
           P H 
          (Zplus (Zmult (Zplus (Zmult v c1) l1) k1)
                 (Zmult (Zplus (Zmult v c2) l2) k2))
        (OMEGA10 v c1 c2 l1 l2 k1 k2)).

Definition fast_OMEGA11 := 
[v1,c1,l1,l2,k1:Z][P:Z -> Prop]
[H : (P (Zplus (Zmult v1 (Zmult c1 k1)) (Zplus (Zmult l1 k1) l2)))]
 (eq_ind_r Z 
   (Zplus (Zmult v1 (Zmult c1 k1)) (Zplus (Zmult l1 k1) l2))
   P H 
   (Zplus (Zmult (Zplus (Zmult v1 c1) l1) k1) l2)
   (OMEGA11 v1 c1 l1 l2 k1)).
Definition fast_OMEGA12 := 
[v2,c2,l1,l2,k2:Z][P:Z -> Prop]
[H : (P (Zplus (Zmult v2 (Zmult c2 k2)) (Zplus l1 (Zmult l2 k2))))]
 (eq_ind_r Z 
   (Zplus (Zmult v2 (Zmult c2 k2)) (Zplus l1 (Zmult l2 k2)))
   P H 
   (Zplus l1 (Zmult (Zplus (Zmult v2 c2) l2) k2))
   (OMEGA12 v2 c2 l1 l2 k2)).

Definition fast_OMEGA15 :=
[v,c1,c2,l1,l2,k2 :Z][P:Z -> Prop]
[H : (P (Zplus (Zmult v (Zplus c1 (Zmult c2 k2))) (Zplus l1 (Zmult l2 k2))))]
 (eq_ind_r Z 
   (Zplus (Zmult v (Zplus c1 (Zmult c2 k2))) (Zplus l1 (Zmult l2 k2)))
   P H 
   (Zplus (Zplus (Zmult v c1) l1) (Zmult (Zplus (Zmult v c2) l2) k2))
   (OMEGA15 v c1 c2 l1 l2 k2)).
Definition fast_OMEGA16 :=
[v,c,l,k :Z][P:Z -> Prop]
[H : (P (Zplus (Zmult v (Zmult c k)) (Zmult l k)))]
 (eq_ind_r Z 
   (Zplus (Zmult v (Zmult c k)) (Zmult l k))
   P H 
   (Zmult (Zplus (Zmult v c) l) k)
   (OMEGA16 v c l k)).

Definition fast_OMEGA13 :=
[v,l1,l2 :Z][x:positive][P:Z -> Prop]
[H : (P (Zplus l1 l2))]
 (eq_ind_r Z 
   (Zplus l1 l2)
   P H 
   (Zplus (Zplus (Zmult v (POS x)) l1) (Zplus (Zmult v (NEG x)) l2))
   (OMEGA13 v l1 l2 x )).

Definition fast_OMEGA14 :=
[v,l1,l2 :Z][x:positive][P:Z -> Prop]
[H : (P (Zplus l1 l2))]
 (eq_ind_r Z 
   (Zplus l1 l2)
   P H 
   (Zplus (Zplus (Zmult v (NEG x)) l1) (Zplus (Zmult v (POS x)) l2))
   (OMEGA14 v l1 l2 x )).
Definition fast_Zred_factor0:=
[x:Z][P:Z -> Prop]
[H : (P (Zmult x (POS xH)) )]
 (eq_ind_r Z 
   (Zmult x (POS xH))
   P H 
   x
   (Zred_factor0 x)).

Definition fast_Zopp_one :=
[x:Z][P:Z -> Prop]
[H : (P (Zmult x (NEG xH)))]
 (eq_ind_r Z 
   (Zmult x (NEG xH))
   P H 
   (Zopp x)
   (Zopp_one x)).

Definition fast_Zmult_sym :=
[x,y :Z][P:Z -> Prop]
[H : (P (Zmult y x))]
 (eq_ind_r Z 
(Zmult y x)
   P H 
(Zmult x y)
   (Zmult_sym x y )).

Definition fast_Zopp_Zplus :=
[x,y :Z][P:Z -> Prop]
[H : (P (Zplus (Zopp x) (Zopp y)) )]
 (eq_ind_r Z 
   (Zplus (Zopp x) (Zopp y))
   P H 
   (Zopp (Zplus x y))
   (Zopp_Zplus x y )).

Definition fast_Zopp_Zopp :=
[x:Z][P:Z -> Prop]
[H : (P x )] (eq_ind_r Z x P H (Zopp (Zopp x)) (Zopp_Zopp x)).

Definition fast_Zopp_Zmult_r :=
[x,y:Z][P:Z -> Prop]
[H : (P (Zmult x (Zopp y)))]
 (eq_ind_r Z 
   (Zmult x (Zopp y))
   P H 
   (Zopp (Zmult x y))
   (Zopp_Zmult_r x y )).

Definition fast_Zmult_plus_distr :=
[n,m,p:Z][P:Z -> Prop]
[H : (P (Zplus (Zmult n p) (Zmult m p)))]
 (eq_ind_r Z 
   (Zplus (Zmult n p) (Zmult m p))
   P H 
   (Zmult (Zplus n m) p)
   (Zmult_plus_distr_l n m p)).
Definition fast_Zmult_Zopp_left:=
[x,y:Z][P:Z -> Prop]
[H : (P (Zmult x (Zopp y)))]
 (eq_ind_r Z 
   (Zmult x (Zopp y))
   P H 
   (Zmult (Zopp x) y)
   (Zmult_Zopp_left x y)).

Definition fast_Zmult_assoc_r :=
[n,m,p :Z][P:Z -> Prop]
[H : (P (Zmult n (Zmult m p)))]
 (eq_ind_r Z 
   (Zmult n (Zmult m p))
   P H 
   (Zmult (Zmult n m) p)
   (Zmult_assoc_r n m p)).

Definition fast_Zred_factor1 :=
[x:Z][P:Z -> Prop]
[H : (P (Zmult x (POS (xO xH))) )]
 (eq_ind_r Z 
   (Zmult x (POS (xO xH)))
   P H 
   (Zplus x x)
   (Zred_factor1 x)).

Definition fast_Zred_factor2 :=
[x,y:Z][P:Z -> Prop]
[H : (P (Zmult x (Zplus (POS xH) y)))]
 (eq_ind_r Z 
   (Zmult x (Zplus (POS xH) y))
   P H 
   (Zplus x (Zmult x y))
   (Zred_factor2 x y)).
Definition fast_Zred_factor3 :=
[x,y:Z][P:Z -> Prop]
[H : (P (Zmult x (Zplus (POS xH) y)))]
 (eq_ind_r Z 
   (Zmult x (Zplus (POS xH) y))
   P H 
   (Zplus (Zmult x y) x)
   (Zred_factor3 x y)).

Definition fast_Zred_factor4 :=
[x,y,z:Z][P:Z -> Prop]
[H : (P (Zmult x (Zplus y z)))]
 (eq_ind_r Z 
   (Zmult x (Zplus y z))
   P H 
   (Zplus (Zmult x y) (Zmult x z))
   (Zred_factor4 x y z)).

Definition fast_Zred_factor5 :=
[x,y:Z][P:Z -> Prop]
[H : (P y)]
 (eq_ind_r Z 
   y
   P H 
   (Zplus (Zmult x ZERO) y)
   (Zred_factor5 x y)).

Definition fast_Zred_factor6 :=
[x :Z][P:Z -> Prop]
[H : (P(Zplus x ZERO) )]
 (eq_ind_r Z 
   (Zplus x ZERO)
   P H 
   x
   (Zred_factor6 x )).

