(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require ZArithRing.
Require ZArith_base.
Require Omega.
Require Wf_nat.
V7only [Import Z_scope.].
Open Local Scope Z_scope.

V7only [Set Implicit Arguments.].

(**********************************************************************)
(** About parity *)

Lemma two_or_two_plus_one : (x:Z) { y:Z | `x = 2*y`}+{ y:Z | `x = 2*y+1`}. 
Proof.
Intro x; NewDestruct x.
Left ; Split with ZERO; Reflexivity.

NewDestruct p.
Right ; Split with (POS p); Reflexivity.

Left ; Split with (POS p); Reflexivity.

Right ; Split with ZERO; Reflexivity.

NewDestruct p.
Right ; Split with (NEG (add xH p)).
Rewrite NEG_xI.
Rewrite NEG_add.
Omega.

Left ; Split with (NEG p); Reflexivity.

Right ; Split with `-1`; Reflexivity.
Qed.

(**********************************************************************)
(** The biggest power of 2 that is stricly less than [a]

    Easy to compute: replace all "1" of the binary representation by
    "0", except the first "1" (or the first one :-) *)

Fixpoint floor_pos [a : positive] : positive :=
  Cases a of
  | xH => xH
  | (xO a') => (xO (floor_pos a'))
  | (xI b') => (xO (floor_pos b'))
  end.

Definition floor := [a:positive](POS (floor_pos a)).

Lemma floor_gt0 : (x:positive) `(floor x) > 0`.
Proof.
Intro.
Compute.
Trivial.
Qed.

Lemma floor_ok : (a:positive) 
  `(floor a) <=  (POS a) < 2*(floor a)`. 
Proof.
Unfold floor.
Intro a; NewInduction a as [p|p|].

Simpl.
Repeat Rewrite POS_xI.
Rewrite (POS_xO (xO (floor_pos p))). 
Rewrite (POS_xO (floor_pos p)).
Omega.

Simpl.
Repeat Rewrite POS_xI.
Rewrite (POS_xO (xO (floor_pos p))).
Rewrite (POS_xO (floor_pos p)).
Rewrite (POS_xO p).
Omega.

Simpl; Omega.
Qed.

(**********************************************************************)
(** Two more induction principles over [Z]. *)

Theorem Z_lt_abs_rec : (P: Z -> Set)
  ((n: Z) ((m: Z) `|m|<|n|` -> (P m)) -> (P n)) -> (p: Z) (P p).
Proof.
Intros P HP p.
LetTac Q:=[z]`0<=z`->(P z)*(P `-z`).
Cut (Q `|p|`);[Intros|Apply (Z_lt_rec Q);Auto with zarith].
Elim (Zabs_dec p);Intro eq;Rewrite eq;Elim H;Auto with zarith.
Unfold Q;Clear Q;Intros.
Apply pair;Apply HP.
Rewrite Zabs_eq;Auto;Intros.
Elim (H `|m|`);Intros;Auto with zarith.
Elim (Zabs_dec m);Intro eq;Rewrite eq;Trivial.
Rewrite Zabs_non_eq;Auto with zarith.
Rewrite Zopp_Zopp;Intros.
Elim (H `|m|`);Intros;Auto with zarith.
Elim (Zabs_dec m);Intro eq;Rewrite eq;Trivial.
Qed.

Theorem Z_lt_abs_induction : (P: Z -> Prop)
  ((n: Z) ((m: Z) `|m|<|n|` -> (P m)) -> (P n)) -> (p: Z) (P p).
Proof.
Intros P HP p.
LetTac Q:=[z]`0<=z`->(P z) /\ (P `-z`).
Cut (Q `|p|`);[Intros|Apply (Z_lt_induction Q);Auto with zarith].
Elim (Zabs_dec p);Intro eq;Rewrite eq;Elim H;Auto with zarith.
Unfold Q;Clear Q;Intros.
Split;Apply HP.
Rewrite Zabs_eq;Auto;Intros.
Elim (H `|m|`);Intros;Auto with zarith.
Elim (Zabs_dec m);Intro eq;Rewrite eq;Trivial.
Rewrite Zabs_non_eq;Auto with zarith.
Rewrite Zopp_Zopp;Intros.
Elim (H `|m|`);Intros;Auto with zarith.
Elim (Zabs_dec m);Intro eq;Rewrite eq;Trivial.
Qed.
V7only [Unset Implicit Arguments.].

(** To do case analysis over the sign of [z] *) 

Lemma Zcase_sign : (x:Z)(P:Prop)
 (`x=0` -> P) ->
 (`x>0` -> P) ->
 (`x<0` -> P) -> P.
Proof.
Intros x P Hzero Hpos Hneg.
Induction x.
Apply Hzero; Trivial.
Apply Hpos; Apply POS_gt_ZERO.
Apply Hneg; Apply NEG_lt_ZERO.
Save.

Lemma sqr_pos : (x:Z)`x*x >= 0`.
Proof.
Intro x.
Apply (Zcase_sign x `x*x >= 0`).
Intros H; Rewrite H; Omega.
Intros H; Replace `0` with `0*0`.
Apply Zge_Zmult_pos_compat; Omega.
Omega.
Intros H; Replace `0` with `0*0`.
Replace `x*x` with `(-x)*(-x)`.
Apply Zge_Zmult_pos_compat; Omega.
Ring.
Omega.
Save.

(**********************************************************************)
(** A list length in Z, tail recursive.  *)

Require PolyList.

Fixpoint Zlength_aux [acc: Z; A:Set; l:(list A)] : Z := Cases l of 
    nil => acc
  | (cons _ l) => (Zlength_aux (Zs acc) A l)
end. 

Definition Zlength := (Zlength_aux 0).
Implicits Zlength [1].

Section Zlength_properties.

Variable A:Set.

Implicit Variable Type l:(list A).

Lemma Zlength_correct : (l:(list A))(Zlength l)=(inject_nat (length l)).
Proof.
Assert (l:(list A))(acc:Z)(Zlength_aux acc A l)=acc+(inject_nat (length l)). 
Induction l.
Simpl; Auto with zarith.
Intros; Simpl (length (cons a l0)); Rewrite inj_S.
Simpl; Rewrite H; Auto with zarith.
Unfold Zlength; Intros; Rewrite H; Auto.
Qed.

Lemma Zlength_nil : (Zlength 1!A (nil A))=0.
Proof.
Auto.
Qed.

Lemma Zlength_cons : (x:A)(l:(list A))(Zlength (cons x l))=(Zs (Zlength l)).
Proof.
Intros; Do 2 Rewrite Zlength_correct.
Simpl (length (cons x l)); Rewrite inj_S; Auto.
Qed.

Lemma Zlength_nil_inv : (l:(list A))(Zlength l)=0 -> l=(nil ?).
Proof.
Intro l; Rewrite Zlength_correct.
Case l; Auto.
Intros x l'; Simpl (length (cons x l')).
Rewrite inj_S.
Intros; ElimType False; Generalize (ZERO_le_inj (length l')); Omega.
Qed.

End Zlength_properties.

Implicits Zlength_correct [1].
Implicits Zlength_cons [1].
Implicits Zlength_nil_inv [1].
