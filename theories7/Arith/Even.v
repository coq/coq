(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Here we define the predicates [even] and [odd] by mutual induction
    and we prove the decidability and the exclusion of those predicates.
    The main results about parity are proved in the module Div2. *)

V7only [Import nat_scope.].
Open Local Scope nat_scope.

Implicit Variables Type m,n:nat.

Inductive even : nat->Prop :=
    even_O : (even O)
  | even_S : (n:nat)(odd n)->(even (S n))
with odd : nat->Prop :=
    odd_S : (n:nat)(even n)->(odd (S n)).

Hint constr_even : arith := Constructors even.
Hint constr_odd : arith := Constructors odd.

Lemma even_or_odd : (n:nat) (even n)\/(odd n).
Proof.
NewInduction n.
Auto with arith.
Elim IHn; Auto with arith.
Qed.

Lemma even_odd_dec : (n:nat) { (even n) }+{ (odd n) }.
Proof.
NewInduction n.
Auto with arith.
Elim IHn; Auto with arith.
Qed.

Lemma not_even_and_odd : (n:nat) (even n) -> (odd n) -> False.
Proof.
NewInduction n.
Intros. Inversion H0.
Intros. Inversion H. Inversion H0. Auto with arith.
Qed.

Lemma even_plus_aux:
  (n,m:nat)
   (iff (odd (plus n m)) (odd n) /\ (even m) \/ (even n) /\ (odd m)) /\
   (iff (even (plus n m)) (even n) /\ (even m) \/ (odd n) /\ (odd m)).
Proof.
Intros n; Elim n; Simpl; Auto with arith.
Intros m; Split; Auto.
Split.
Intros H; Right; Split; Auto with arith.
Intros H'; Case H'; Auto with arith.
Intros H'0; Elim H'0; Intros H'1 H'2; Inversion H'1.
Intros H; Elim H; Auto.
Split; Auto with arith.
Intros H'; Elim H'; Auto with arith.
Intros H; Elim H; Auto.
Intros H'0; Elim H'0; Intros H'1 H'2; Inversion H'1.
Intros n0 H' m; Elim (H' m); Intros H'1 H'2; Elim H'1; Intros E1 E2; Elim H'2;
 Intros E3 E4; Clear H'1 H'2.
Split; Split.
Intros H'0; Case E3.
Inversion H'0; Auto.
Intros H; Elim H; Intros H0 H1; Clear H; Auto with arith.
Intros H; Elim H; Intros H0 H1; Clear H; Auto with arith.
Intros H'0; Case H'0; Intros C0; Case C0; Intros C1 C2.
Apply odd_S.
Apply E4; Left; Split; Auto with arith.
Inversion C1; Auto.
Apply odd_S.
Apply E4; Right; Split; Auto with arith.
Inversion C1; Auto.
Intros H'0.
Case E1.
Inversion H'0; Auto.
Intros H; Elim H; Intros H0 H1; Clear H; Auto with arith.
Intros H; Elim H; Intros H0 H1; Clear H; Auto with arith.
Intros H'0; Case H'0; Intros C0; Case C0; Intros C1 C2.
Apply even_S.
Apply E2; Left; Split; Auto with arith.
Inversion C1; Auto.
Apply even_S.
Apply E2; Right; Split; Auto with arith.
Inversion C1; Auto.
Qed.
 
Lemma even_even_plus : (n,m:nat) (even n) -> (even m) -> (even (plus n m)).
Proof.
Intros n m; Case (even_plus_aux n m).
Intros H H0; Case H0; Auto.
Qed.
 
Lemma odd_even_plus : (n,m:nat) (odd n) -> (odd m) -> (even (plus n m)).
Proof.
Intros n m; Case (even_plus_aux n m).
Intros H H0; Case H0; Auto.
Qed.
 
Lemma even_plus_even_inv_r :
  (n,m:nat) (even (plus n m)) -> (even n) -> (even m).
Proof.
Intros n m H; Case (even_plus_aux n m).
Intros H' H'0; Elim H'0.
Intros H'1; Case H'1; Auto.
Intros H0; Elim H0; Auto.
Intros H0 H1 H2; Case (not_even_and_odd n); Auto.
Case H0; Auto.
Qed.
 
Lemma even_plus_even_inv_l :
  (n,m:nat) (even (plus n m)) -> (even m) -> (even n).
Proof.
Intros n m H; Case (even_plus_aux n m).
Intros H' H'0; Elim H'0.
Intros H'1; Case H'1; Auto.
Intros H0; Elim H0; Auto.
Intros H0 H1 H2; Case (not_even_and_odd m); Auto.
Case H0; Auto.
Qed.
 
Lemma even_plus_odd_inv_r : (n,m:nat) (even (plus n m)) -> (odd n) -> (odd m).
Proof.
Intros n m H; Case (even_plus_aux n m).
Intros H' H'0; Elim H'0.
Intros H'1; Case H'1; Auto.
Intros H0 H1 H2; Case (not_even_and_odd n); Auto.
Case H0; Auto.
Intros H0; Case H0; Auto.
Qed.
 
Lemma even_plus_odd_inv_l : (n,m:nat) (even (plus n m)) -> (odd m) -> (odd n).
Proof.
Intros n m H; Case (even_plus_aux n m).
Intros H' H'0; Elim H'0.
Intros H'1; Case H'1; Auto.
Intros H0 H1 H2; Case (not_even_and_odd m); Auto.
Case H0; Auto.
Intros H0; Case H0; Auto.
Qed.
Hints Resolve even_even_plus odd_even_plus :arith.
 
Lemma odd_plus_l : (n,m:nat) (odd n) -> (even m) -> (odd (plus n m)).
Proof.
Intros n m; Case (even_plus_aux n m).
Intros H; Case H; Auto.
Qed.
 
Lemma odd_plus_r : (n,m:nat) (even n) -> (odd m) -> (odd (plus n m)).
Proof.
Intros n m; Case (even_plus_aux n m).
Intros H; Case H; Auto.
Qed.
 
Lemma odd_plus_even_inv_l : (n,m:nat) (odd (plus n m)) -> (odd m) -> (even n).
Proof.
Intros n m H; Case (even_plus_aux n m).
Intros H' H'0; Elim H'.
Intros H'1; Case H'1; Auto.
Intros H0 H1 H2; Case (not_even_and_odd m); Auto.
Case H0; Auto.
Intros H0; Case H0; Auto.
Qed.
 
Lemma odd_plus_even_inv_r : (n,m:nat) (odd (plus n m)) -> (odd n) -> (even m).
Proof.
Intros n m H; Case (even_plus_aux n m).
Intros H' H'0; Elim H'.
Intros H'1; Case H'1; Auto.
Intros H0; Case H0; Auto.
Intros H0 H1 H2; Case (not_even_and_odd n); Auto.
Case H0; Auto.
Qed.
 
Lemma odd_plus_odd_inv_l : (n,m:nat) (odd (plus n m)) -> (even m) -> (odd n).
Proof.
Intros n m H; Case (even_plus_aux n m).
Intros H' H'0; Elim H'.
Intros H'1; Case H'1; Auto.
Intros H0; Case H0; Auto.
Intros H0 H1 H2; Case (not_even_and_odd m); Auto.
Case H0; Auto.
Qed.
 
Lemma odd_plus_odd_inv_r : (n,m:nat) (odd (plus n m)) -> (even n) -> (odd m).
Proof.
Intros n m H; Case (even_plus_aux n m).
Intros H' H'0; Elim H'.
Intros H'1; Case H'1; Auto.
Intros H0 H1 H2; Case (not_even_and_odd n); Auto.
Case H0; Auto.
Intros H0; Case H0; Auto.
Qed.
Hints Resolve odd_plus_l odd_plus_r :arith.
 
Lemma even_mult_aux :
  (n,m:nat)
   (iff (odd (mult n m)) (odd n) /\ (odd m)) /\
   (iff (even (mult n m)) (even n) \/ (even m)).
Proof.
Intros n; Elim n; Simpl; Auto with arith.
Intros m; Split; Split; Auto with arith.
Intros H'; Inversion H'.
Intros H'; Elim H'; Auto.
Intros n0 H' m; Split; Split; Auto with arith.
Intros H'0.
Elim (even_plus_aux m (mult n0 m)); Intros H'3 H'4; Case H'3; Intros H'1 H'2;
 Case H'1; Auto.
Intros H'5; Elim H'5; Intros H'6 H'7; Auto with arith.
Split; Auto with arith.
Case (H' m).
Intros H'8 H'9; Case H'9.
Intros H'10; Case H'10; Auto with arith.
Intros H'11 H'12; Case (not_even_and_odd m); Auto with arith.
Intros H'5; Elim H'5; Intros H'6 H'7; Case (not_even_and_odd (mult n0 m)); Auto.
Case (H' m).
Intros H'8 H'9; Case H'9; Auto.
Intros H'0; Elim H'0; Intros H'1 H'2; Clear H'0.
Elim (even_plus_aux m (mult n0 m)); Auto.
Intros H'0 H'3.
Elim H'0.
Intros H'4 H'5; Apply H'5; Auto.
Left; Split; Auto with arith.
Case (H' m).
Intros H'6 H'7; Elim H'7.
Intros H'8 H'9; Apply H'9.
Left.
Inversion H'1; Auto.
Intros H'0.
Elim (even_plus_aux m (mult n0 m)); Intros H'3 H'4; Case H'4.
Intros H'1 H'2.
Elim H'1; Auto.
Intros H; Case H; Auto.
Intros H'5; Elim H'5; Intros H'6 H'7; Auto with arith.
Left.
Case (H' m).
Intros H'8; Elim H'8.
Intros H'9; Elim H'9; Auto with arith.
Intros H'0; Elim H'0; Intros H'1.
Case (even_or_odd m); Intros H'2.
Apply even_even_plus; Auto.
Case (H' m).
Intros H H0; Case H0; Auto.
Apply odd_even_plus; Auto.
Inversion H'1; Case (H' m); Auto.
Intros H1; Case H1; Auto.
Apply even_even_plus; Auto.
Case (H' m).
Intros H H0; Case H0; Auto.
Qed.
 
Lemma even_mult_l : (n,m:nat) (even n) -> (even (mult n m)).
Proof.
Intros n m; Case (even_mult_aux n m); Auto.
Intros H H0; Case H0; Auto.
Qed.
 
Lemma even_mult_r: (n,m:nat) (even m) -> (even (mult n m)).
Proof.
Intros n m; Case (even_mult_aux n m); Auto.
Intros H H0; Case H0; Auto.
Qed.
Hints Resolve even_mult_l even_mult_r :arith.
 
Lemma even_mult_inv_r: (n,m:nat) (even (mult n m)) -> (odd n) -> (even m).
Proof.
Intros n m H' H'0.
Case (even_mult_aux n m).
Intros H'1 H'2; Elim H'2.
Intros H'3; Elim H'3; Auto.
Intros H; Case (not_even_and_odd n); Auto.
Qed.
 
Lemma even_mult_inv_l : (n,m:nat) (even (mult n m)) -> (odd m) -> (even n).
Proof.
Intros n m H' H'0.
Case (even_mult_aux n m).
Intros H'1 H'2; Elim H'2.
Intros H'3; Elim H'3; Auto.
Intros H; Case (not_even_and_odd m); Auto.
Qed.
 
Lemma odd_mult : (n,m:nat) (odd n) -> (odd m) -> (odd (mult n m)).
Proof.
Intros n m; Case (even_mult_aux n m); Intros H; Case H; Auto.
Qed.
Hints Resolve even_mult_l even_mult_r odd_mult :arith.
 
Lemma odd_mult_inv_l : (n,m:nat) (odd (mult n m)) -> (odd n).
Proof.
Intros n m H'.
Case (even_mult_aux n m).
Intros H'1 H'2; Elim H'1.
Intros H'3; Elim H'3; Auto.
Qed.
 
Lemma odd_mult_inv_r : (n,m:nat) (odd (mult n m)) -> (odd m).
Proof.
Intros n m H'.
Case (even_mult_aux n m).
Intros H'1 H'2; Elim H'1.
Intros H'3; Elim H'3; Auto.
Qed.

